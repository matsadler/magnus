use magnus::{Error, RArray, RClass, RModule, Value, prelude::*, rb_assert};

#[test]
fn it_checks_and_removes_constants() -> Result<(), Error> {
    let ruby = unsafe { magnus::embed::init() };

    let parent = RClass::new(ruby.class_object())?;
    parent.const_set("INHERITED", 42)?;
    let child = RClass::new(parent)?;
    assert!(child.const_defined("INHERITED")?);
    assert!(!child.const_defined("MISSING_CONSTANT")?);
    let err = child.remove_const::<_, Value>("INHERITED").unwrap_err();
    assert!(err.is_kind_of(ruby.exception_name_error()));
    assert_eq!(parent.const_get::<_, i64>("INHERITED")?, 42);

    child.const_set("INHERITED", 7)?;
    assert_eq!(child.remove_const::<_, i64>("INHERITED")?, 7);
    assert!(child.const_defined("INHERITED")?);
    assert_eq!(child.const_get::<_, i64>("INHERITED")?, 42);

    let included = ruby.module_new();
    included.const_set("INCLUDED", 1)?;
    child.include_module(included)?;
    assert!(child.const_defined("INCLUDED")?);

    let module = ruby.module_new();
    assert!(module.const_defined("Object")?);
    module.const_set("PRIVATE_VALUE", 1)?;
    let _: Value = module.funcall("private_constant", ("PRIVATE_VALUE",))?;
    assert!(module.const_defined("PRIVATE_VALUE")?);
    assert_eq!(module.remove_const::<_, i64>("PRIVATE_VALUE")?, 1);

    let original = ruby.ary_new();
    let name = ruby.intern("LOCAL_VALUE");
    module.const_set(name, original)?;
    assert!(module.const_defined(name)?);
    let removed: RArray = module.remove_const(ruby.to_symbol("LOCAL_VALUE"))?;
    rb_assert!(ruby, "removed.equal?(original)", removed, original);
    assert!(!module.const_defined(name)?);

    let err = module.remove_const::<_, Value>(name).unwrap_err();
    assert!(err.is_kind_of(ruby.exception_name_error()));
    for invalid in ["lowercase", "Nested::Value"] {
        let err = module.remove_const::<_, Value>(invalid).unwrap_err();
        assert!(err.is_kind_of(ruby.exception_name_error()));
    }

    let nested = ruby.module_new();
    nested.const_set("VALUE", 1)?;
    module.const_set("Nested", nested)?;
    assert!(module.const_defined("Nested")?);
    assert!(!module.const_defined("Nested::VALUE")?);
    rb_assert!(ruby, "mod.const_defined?('Nested::VALUE')", mod = module);

    let _: Value = module.funcall(
        "autoload",
        (
            ruby.to_symbol("LAZY_VALUE"),
            "/nonexistent/magnus-constant-autoload.rb",
        ),
    )?;
    assert!(module.const_defined("LAZY_VALUE")?);
    let removed: Value = module.remove_const("LAZY_VALUE")?;
    assert!(removed.is_nil());
    assert!(!module.const_defined("LAZY_VALUE")?);

    module.const_set("WRONG_TYPE", 42)?;
    let err = module.remove_const::<_, RArray>("WRONG_TYPE").unwrap_err();
    assert!(err.is_kind_of(ruby.exception_type_error()));
    assert!(!module.const_defined("WRONG_TYPE")?);

    module.const_set("FROZEN_VALUE", 42)?;
    module.freeze();
    let err = module.remove_const::<_, Value>("FROZEN_VALUE").unwrap_err();
    assert!(err.is_kind_of(ruby.exception_frozen_error()));
    assert_eq!(module.const_get::<_, i64>("FROZEN_VALUE")?, 42);

    let overridden: RModule = ruby.eval(
        "Module.new do
           def self.const_defined?(*); false; end
           def self.remove_const(*); raise 'Ruby override called'; end
         end",
    )?;
    overridden.const_set("NATIVE_VALUE", 42)?;
    assert!(overridden.const_defined("NATIVE_VALUE")?);
    assert_eq!(overridden.remove_const::<_, i64>("NATIVE_VALUE")?, 42);

    Ok(())
}

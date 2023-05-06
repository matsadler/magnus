use magnus::{prelude::*, r_struct::RStruct, rb_assert};

#[test]
fn it_defines_a_struct() {
    let ruby = unsafe { magnus::embed::init() };

    let struct_class = ruby.define_struct(Some("Foo"), ("bar", "baz")).unwrap();

    rb_assert!(ruby, r#"val.name == "Struct::Foo""#, val = struct_class);
    rb_assert!(ruby, "val.members == [:bar, :baz]", val = struct_class);

    let obj = struct_class.new_instance((1, 2)).unwrap();

    rb_assert!(ruby, "val.bar == 1", val = obj);
    rb_assert!(ruby, "val.baz == 2", val = obj);

    rb_assert!(
        ruby,
        r#"val.name == nil"#,
        val = ruby.define_struct(None, ("foo",)).unwrap()
    );

    let obj = RStruct::from_value(obj).unwrap();
    assert_eq!(1, obj.get(0).unwrap());
    assert_eq!(2, obj.get(1).unwrap());

    assert_eq!(&["bar", "baz"], obj.members().unwrap().as_slice())
}

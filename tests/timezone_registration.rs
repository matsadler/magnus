#![cfg(feature = "jiff-zoned")]

use std::sync::LazyLock;

use magnus::{Error, Module, RClass, Ruby, Value, value::ReprValue};

#[test]
fn timezone_registration() {
    Ruby::init(|ruby| {
        reinitialization_keeps_the_registered_timezone(ruby)?;
        versioned_constant_collision_is_ignored(ruby)?;
        foreign_alias_is_preserved(ruby)?;
        absent_alias_is_installed(ruby)?;
        older_magnus_alias_is_replaced(ruby)?;
        equal_or_newer_magnus_alias_is_preserved(ruby)?;
        Ok::<_, Error>(())
    })
    .unwrap();
}

static VERSIONED_NAME: LazyLock<String> = LazyLock::new(|| {
    format!(
        "TimeZoneMagnus_{}",
        env!("CARGO_PKG_VERSION").replace('.', "_")
    )
});

fn replace_alias(ruby: &Ruby, class: RClass) -> Result<(), Error> {
    let object = ruby.class_object();
    object.remove_const("Timezone")?;
    object.const_set("Timezone", class)
}

fn reinitialization_keeps_the_registered_timezone(ruby: &Ruby) -> Result<(), Error> {
    let before: RClass = ruby.eval("Timezone")?;
    magnus::init_features(ruby)?;
    assert!(magnus::eval!(ruby, "Timezone.equal?(before)", before)?);
    Ok(())
}

fn versioned_constant_collision_is_ignored(ruby: &Ruby) -> Result<(), Error> {
    let object = ruby.class_object();
    let original: RClass = ruby.eval("Timezone")?;
    let foreign: RClass = ruby.eval("Class.new")?;
    object.remove_const(VERSIONED_NAME.as_str())?;
    object.const_set(VERSIONED_NAME.as_str(), foreign)?;
    ruby.eval::<Value>("def Time.find_timezone(_name); :collision; end")?;
    magnus::init_features(ruby)?;
    assert!(ruby.eval::<bool>("Time.find_timezone('UTC') == :collision")?);
    assert!(magnus::eval!(
        ruby,
        "Timezone.equal?(expected)",
        expected = original
    )?);
    assert!(
        object
            .const_get::<_, Value>(VERSIONED_NAME.as_str())?
            .funcall::<_, _, bool>("equal?", (foreign,))?
    );
    object.remove_const(VERSIONED_NAME.as_str())?;
    object.const_set(VERSIONED_NAME.as_str(), original)?;
    Ok(())
}

fn foreign_alias_is_preserved(ruby: &Ruby) -> Result<(), Error> {
    let original: RClass = ruby.eval("Timezone")?;
    let foreign: RClass = ruby.eval("Class.new")?;
    replace_alias(ruby, foreign)?;
    magnus::init_features(ruby)?;
    assert!(magnus::eval!(
        ruby,
        "Timezone.equal?(expected)",
        expected = foreign
    )?);
    assert!(
        ruby.class_object()
            .const_get::<_, Value>(VERSIONED_NAME.as_str())?
            .funcall::<_, _, bool>("equal?", (original,))?
    );

    ruby.eval::<Value>("def Time.find_timezone(_name); :foreign; end")?;
    magnus::init_features(ruby)?;
    assert!(ruby.eval::<bool>("Time.find_timezone('UTC') == :foreign")?);
    Ok(())
}

fn absent_alias_is_installed(ruby: &Ruby) -> Result<(), Error> {
    let original: RClass = ruby.class_object().const_get(VERSIONED_NAME.as_str())?;
    ruby.class_object().remove_const("Timezone")?;
    magnus::init_features(ruby)?;
    assert!(magnus::eval!(
        ruby,
        "Timezone.equal?(expected)",
        expected = original
    )?);
    Ok(())
}

fn older_magnus_alias_is_replaced(ruby: &Ruby) -> Result<(), Error> {
    let original: RClass = ruby.eval("Timezone")?;
    let older: RClass = ruby.eval("Class.new")?;
    older.const_set("MAGNUS_JIFF_VERSION", "0.8.0")?;
    replace_alias(ruby, older)?;
    ruby.eval::<Value>("def Time.find_timezone(_name); :old; end")?;
    magnus::init_features(ruby)?;
    assert!(magnus::eval!(
        ruby,
        "Timezone.equal?(expected)",
        expected = original
    )?);
    assert!(ruby.eval::<bool>("Time.find_timezone('UTC').instance_of?(Timezone)")?);
    Ok(())
}

fn equal_or_newer_magnus_alias_is_preserved(ruby: &Ruby) -> Result<(), Error> {
    let original: RClass = ruby.eval("Timezone")?;
    for version in [env!("CARGO_PKG_VERSION"), "999.0.0"] {
        let existing: RClass = ruby.eval("Class.new")?;
        existing.const_set("MAGNUS_JIFF_VERSION", version)?;
        replace_alias(ruby, existing)?;
        ruby.eval::<Value>("def Time.find_timezone(_name); :current; end")?;
        magnus::init_features(ruby)?;
        assert!(magnus::eval!(
            ruby,
            "Timezone.equal?(expected)",
            expected = existing
        )?);
        assert!(ruby.eval::<bool>("Time.find_timezone('UTC') == :current")?);
    }
    replace_alias(ruby, original)?;
    Ok(())
}

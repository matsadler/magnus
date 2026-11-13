//! Ruby constructors for Jiff timezones, using Magnus's native backing type.
//!
//! `require "jiff_magnus"` calls [`init`] and bundles IANA timezone data.
//! The gem subclasses Magnus's [`JiffTimeZone`] to reuse its timezone methods.
//! Core [`jiff::ZonedDateTime`] conversions work before this gem is initialized.

use std::sync::{Mutex, OnceLock};

use jiff::tz::TimeZone;
use magnus::{
    Error, RArray, RClass, RModule, Ruby, TypedData, Value, prelude::*, rb_sys::AsRawValue,
    time::JiffTimeZone, typed_data::Obj, value::Opaque,
};

const CLASS_NAME: &str = "JiffTimezone";
const AUTO_TIME_REGISTRATION_ENV: &str = "JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION";

struct Initialization {
    // Cache the published class to detect removal or replacement on repeated init calls.
    class: Opaque<RClass>,
    // Keep the expected Time.find_timezone method in a GC-rooted, mutable Ruby holder.
    // Registration replaces its entry; nil means init should skip method validation.
    resolver: Opaque<RArray>,
}

fn validate_class(ruby: &Ruby, expected: RClass) -> Result<(), Error> {
    let object = ruby.class_object();
    if !object.const_defined(CLASS_NAME)? {
        return Err(conflict(ruby, "JiffTimezone initialization was removed"));
    }
    let class: Value = object.const_get(CLASS_NAME)?;
    if class.as_raw() != expected.as_raw() {
        return Err(conflict(ruby, "JiffTimezone initialization was replaced"));
    }
    Ok(())
}

static INITIALIZATION: OnceLock<Initialization> = OnceLock::new();
// Ruby definition hooks can reenter either public entry point while it publishes
// or restores definitions. Reject those calls before they can commit the cache.
static INITIALIZATION_LOCK: Mutex<()> = Mutex::new(());
static RESOLVER_OBSERVER: OnceLock<Opaque<RModule>> = OnceLock::new();

/// Initializes `JiffTimezone` with optional automatic `Time.find_timezone` lookup.
///
/// When an existing `JiffTimezone` inherits from this Magnus copy's timezone
/// class, this function reuses it and leaves its public methods untouched. It
/// preserves an existing `Time.find_timezone`, even if the method is private.
/// Otherwise, it adds lookup unless you set
/// `JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION` to `0` or `false`
/// (case-insensitive) before initialization. Constructors remain available
/// without automatic lookup. Use [`register`] to explicitly install or replace
/// the method regardless of this setting.
///
/// # Errors
///
/// We return Ruby `LoadError` in these cases:
///
/// - An existing `Object::JiffTimezone` belongs to a different native
///   implementation.
/// - Ruby code removed or replaced `JiffTimezone` or a tracked
///   `Time.find_timezone` method after initialization.
/// - Initialization or registration is already in progress.
/// - A prepended method-added hook prevents tracking resolver installation.
///
/// Ruby allocation and method errors propagate. If publishing the class or
/// resolver fails, this function rolls back only definitions it added.
#[cfg_attr(not(test), magnus::init(name = "jiff_magnus"))]
pub fn init(ruby: &Ruby) -> Result<(), Error> {
    let _guard = INITIALIZATION_LOCK.try_lock().map_err(|_| {
        conflict(
            ruby,
            "timezone initialization or registration is already in progress",
        )
    })?;
    if let Some(existing) = INITIALIZATION.get() {
        validate_class(ruby, ruby.get_inner(existing.class))?;
        let expected: Option<Value> = ruby.get_inner(existing.resolver).entry(0)?;
        if let Some(expected) = expected {
            let time = ruby.class_time();
            if !time.respond_to("find_timezone", true)? {
                return Err(conflict(ruby, "Time.find_timezone was removed"));
            }
            let method: Value = time.funcall("method", ("find_timezone",))?;
            if !method.funcall::<_, _, bool>("==", (expected,))? {
                return Err(conflict(ruby, "Time.find_timezone was replaced"));
            }
        }
        return Ok(());
    }
    let object = ruby.class_object();
    let env: Value = object.const_get("ENV")?;
    let setting: Option<String> = env.funcall("[]", (AUTO_TIME_REGISTRATION_ENV,))?;
    let auto_register = !setting
        .as_deref()
        .is_some_and(|value| value == "0" || value.eq_ignore_ascii_case("false"));
    let existing_class = if object.const_defined(CLASS_NAME)? {
        let value: Value = object.const_get(CLASS_NAME)?;
        let class = RClass::from_value(value)
            .filter(|class| class.is_inherited(JiffTimeZone::class(ruby)))
            .ok_or_else(|| {
                conflict(
                    ruby,
                    "JiffTimezone is already defined by an incompatible native implementation",
                )
            })?;
        Some(class)
    } else {
        None
    };
    let time = ruby.class_time();

    // Configure a new class before publishing it; never modify a reused class.
    let class = if let Some(class) = existing_class {
        class
    } else {
        // Reuse Magnus's TypedData instead of introducing a second native payload.
        let class = RClass::new(JiffTimeZone::class(ruby))?;
        class.undef_default_alloc_func();
        class.define_singleton_method("find_timezone", magnus::function!(find_timezone, 1))?;
        class.define_singleton_method("utc", magnus::function!(utc, 0))?;
        class.define_singleton_method("unknown", magnus::function!(unknown, 0))?;
        class.define_singleton_method("fixed", magnus::function!(fixed, 1))?;
        class.define_singleton_method("posix", magnus::function!(posix, 1))?;
        class.define_singleton_method("register", magnus::function!(register, 0))?;
        class.freeze();
        class
    };
    let resolver = (|| -> Result<Value, Error> {
        if existing_class.is_none() {
            object.const_set(CLASS_NAME, class)?;
        }
        validate_class(ruby, class)?;
        let method = if !auto_register {
            ruby.qnil().as_value()
        } else if time.respond_to("find_timezone", true)? {
            time.funcall("method", ("find_timezone",))?
        } else {
            install_resolver(ruby, class)?
        };
        validate_class(ruby, class)?;
        Ok(method)
    })();
    let resolver = match resolver {
        Ok(resolver) => resolver,
        Err(error) => {
            // The resolver installer rolls back its own changes. A class hook
            // may instead have installed application definitions before raising.
            if existing_class.is_none() {
                let _ = (|| -> Result<(), Error> {
                    if object.const_defined(CLASS_NAME)? {
                        let current: Value = object.const_get(CLASS_NAME)?;
                        if current.as_raw() == class.as_raw() {
                            object.remove_const::<_, Value>(CLASS_NAME)?;
                        }
                    }
                    Ok(())
                })();
            }
            return Err(error);
        }
    };
    // A Ruby holder keeps the current method alive without retaining every
    // method replaced by explicit registration.
    let resolver = ruby.ary_new_from_values(&[resolver]);
    ruby.gc_register_mark_object(class);
    ruby.gc_register_mark_object(resolver);
    INITIALIZATION
        .set(Initialization {
            class: class.into(),
            resolver: resolver.into(),
        })
        .map_err(|_| conflict(ruby, "timezone initialization is already in progress"))?;
    Ok(())
}

/// Replaces `Time.find_timezone` with this companion's Jiff name lookup.
///
/// Unlike [`init`], this explicitly overrides an existing method, including a
/// private one, regardless of `JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION`.
/// Ruby callers use `JiffTimezone.register`. Calling this before initialization
/// first initializes the companion.
///
/// # Errors
///
/// Returns `LoadError` if Ruby code removed or replaced the initialized class,
/// initialization or registration is already in progress, or a prepended
/// method-added hook prevents tracking the replacement.
/// Ruby errors propagate. A failed replacement restores the previous method
/// unless a Ruby hook has installed another definition.
pub fn register(ruby: &Ruby) -> Result<(), Error> {
    if INITIALIZATION.get().is_none() {
        init(ruby)?;
    }
    let _guard = INITIALIZATION_LOCK.try_lock().map_err(|_| {
        conflict(
            ruby,
            "timezone initialization or registration is already in progress",
        )
    })?;
    let initialization = INITIALIZATION.get().expect("companion was initialized");
    let class = ruby.get_inner(initialization.class);
    validate_class(ruby, class)?;
    let method = install_resolver(ruby, class)?;
    ruby.get_inner(initialization.resolver).store(0, method)
}

fn resolver_observer(ruby: &Ruby, singleton: RClass) -> Result<RModule, Error> {
    if let Some(observer) = RESOLVER_OBSERVER.get() {
        return Ok(ruby.get_inner(*observer));
    }
    // Reuse one anonymous ancestor; registration removes its temporary hook.
    let observer = ruby.module_new();
    singleton.funcall::<_, _, Value>("prepend", (observer,))?;
    ruby.gc_register_mark_object(observer);
    RESOLVER_OBSERVER
        .set(observer.into())
        .map_err(|_| conflict(ruby, "resolver observer was already initialized"))?;
    Ok(observer)
}

fn install_resolver(ruby: &Ruby, class: RClass) -> Result<Value, Error> {
    let time = ruby.class_time();
    let singleton = time.singleton_class()?;
    let previous: Option<Value> = if time.respond_to("find_timezone", true)? {
        Some(time.funcall("method", ("find_timezone",))?)
    } else {
        None
    };
    let visibility = resolver_visibility(singleton)?;
    let previous = if visibility.is_some() {
        singleton_resolver(singleton)?
    } else {
        previous
    };
    let observer = resolver_observer(ruby, singleton)?;
    // Capture the installed method before application hooks run, then compare
    // UnboundMethods during rollback. Each Ruby closure identifies one install.
    let prototype = ruby.module_new();
    prototype.define_method("find_timezone", magnus::function!(find_timezone, 1))?;
    let lookup: Value = prototype.funcall("instance_method", ("find_timezone",))?;
    let lookup: Value = lookup.funcall("bind", (time,))?;
    let installed = ruby.ary_new();
    let factory: Value = prototype.funcall(
        "module_eval",
        (r#"->(lookup, time, observer, installed) {
            definition = ->(name) { lookup.call(name) }
            -> {
                observer.send(:define_method, :singleton_method_added) do |name|
                    if name == :find_timezone && installed.empty?
                        singleton = time.singleton_class
                        method = singleton.instance_method(name)
                        method = method.super_method until method.owner.equal?(singleton)
                        installed << method
                    end
                    super(name)
                end
                begin
                    observer.send(:private, :singleton_method_added)
                    singleton = time.singleton_class
                    unless singleton.instance_method(:singleton_method_added).owner.equal?(observer)
                        raise LoadError, 'prepended singleton_method_added prevents resolver rollback tracking'
                    end
                    singleton.send(:define_method, :find_timezone, definition)
                ensure
                    observer.send(:remove_method, :singleton_method_added)
                end
            }
        }"#,),
    )?;
    let install: Value = factory.funcall("call", (lookup, time, observer, installed))?;
    let result = (|| {
        install.funcall::<_, _, Value>("call", ())?;
        let method = time.funcall("method", ("find_timezone",))?;
        validate_class(ruby, class)?;
        Ok(method)
    })();
    if result.is_err() {
        let owns_current = (|| -> Result<bool, Error> {
            let expected: Option<Value> = installed.entry(0)?;
            match expected {
                Some(expected) => match singleton_resolver(singleton)? {
                    Some(current) => current.funcall("==", (expected,)),
                    None => Ok(false),
                },
                None => Ok(false),
            }
        })()
        .unwrap_or(false);
        if owns_current {
            let _ = singleton.funcall::<_, _, Value>("remove_method", ("find_timezone",));
            // Removal hooks may install application methods that rollback must preserve.
            if !matches!(resolver_visibility(singleton), Ok(None)) {
                return result;
            }
            // Removing a replacement can expose an ancestor hidden by undef_method.
            if previous.is_none() && time.respond_to("find_timezone", true).unwrap_or(false) {
                let _ = singleton.funcall::<_, _, Value>("undef_method", ("find_timezone",));
            }
            if let (Some(method), Some(access)) = (previous, visibility) {
                // Restore visibility before application hooks run, so their
                // subsequent visibility changes remain intact even on error.
                let _ = (|| -> Result<(), Error> {
                    let restore: Value = prototype.funcall(
                        "module_eval",
                        (r#"->(singleton, method, access) {
                            singleton.class_eval do
                                send(access)
                                define_method(:find_timezone, method)
                            end
                        }"#,),
                    )?;
                    restore.funcall::<_, _, Value>("call", (singleton, method, access))?;
                    Ok(())
                })();
            }
        }
    }
    result
}

fn singleton_resolver(singleton: RClass) -> Result<Option<Value>, Error> {
    if resolver_visibility(singleton)?.is_none() {
        return Ok(None);
    }
    let mut method: Option<Value> = singleton.funcall("instance_method", ("find_timezone",))?;
    while let Some(current) = method {
        let owner: Value = current.funcall("owner", ())?;
        if owner.as_raw() == singleton.as_raw() {
            return Ok(Some(current));
        }
        method = current.funcall("super_method", ())?;
    }
    Ok(None)
}

fn resolver_visibility(singleton: RClass) -> Result<Option<&'static str>, Error> {
    for (query, access) in [
        ("public_method_defined?", "public"),
        ("protected_method_defined?", "protected"),
        ("private_method_defined?", "private"),
    ] {
        if singleton.funcall::<_, _, bool>(query, ("find_timezone", false))? {
            return Ok(Some(access));
        }
    }
    Ok(None)
}

fn conflict(ruby: &Ruby, message: &str) -> Error {
    Error::new(ruby.exception_load_error(), message.to_owned())
}

fn wrap(ruby: &Ruby, zone: TimeZone) -> Result<Obj<JiffTimeZone>, Error> {
    let class = INITIALIZATION
        .get()
        .map(|initialization| ruby.get_inner(initialization.class))
        .ok_or_else(|| conflict(ruby, "call jiff_magnus::init before using constructors"))?;
    let object = ruby.obj_wrap_as(JiffTimeZone::new(zone), class);
    object.freeze();
    Ok(object)
}

fn find_timezone(ruby: &Ruby, name: String) -> Result<Option<Obj<JiffTimeZone>>, Error> {
    TimeZone::get(&name)
        .ok()
        .map(|zone| wrap(ruby, zone))
        .transpose()
}

fn utc(ruby: &Ruby) -> Result<Obj<JiffTimeZone>, Error> {
    wrap(ruby, TimeZone::UTC)
}

fn unknown(ruby: &Ruby) -> Result<Obj<JiffTimeZone>, Error> {
    wrap(ruby, TimeZone::unknown())
}

fn fixed(ruby: &Ruby, seconds: i32) -> Result<Obj<JiffTimeZone>, Error> {
    let offset = jiff::tz::Offset::from_seconds(seconds)
        .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
    wrap(ruby, TimeZone::fixed(offset))
}

fn posix(ruby: &Ruby, rule: String) -> Result<Obj<JiffTimeZone>, Error> {
    let zone = TimeZone::posix(&rule)
        .map_err(|err| Error::new(ruby.exception_arg_error(), err.to_string()))?;
    wrap(ruby, zone)
}

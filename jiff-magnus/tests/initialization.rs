// Each companion instance has its own cache, while all three use the same
// Magnus backing type. This exercises reuse without foreign Rust payloads.
#[path = "../src/lib.rs"]
mod second_provider;
#[path = "../src/lib.rs"]
mod third_provider;

use std::{env, process::Command, thread};

use jiff_magnus::{init, register};
use magnus::{
    Error, RClass, Ruby, Time, TryConvert, TypedData, Value, prelude::*, rb_assert,
    time::JiffTimeZone,
};

// Ruby can initialize only once per process. Run each scenario in a fresh
// process so cache state and irreversible changes such as Time.freeze stay local.
fn with_fresh_ruby(scenario: fn(&Ruby) -> Result<(), Error>) {
    const CASE_ENV: &str = "JIFF_MAGNUS_INITIALIZATION_TEST";
    let current = thread::current();
    let name = current.name().expect("test thread must have a name");
    if env::var(CASE_ENV).as_deref() == Ok(name) {
        return Ruby::init(scenario).unwrap();
    }

    let output = Command::new(env::current_exe().unwrap())
        .args(["--exact", name, "--nocapture"])
        .env(CASE_ENV, name)
        .env_remove("JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION")
        .output()
        .expect("initialization test process must start");
    assert!(
        output.status.success(),
        "{name} failed ({}):\n{}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn incompatible_class_is_rejected_before_defining_a_resolver() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.eval::<Value>("class JiffTimezone; end")?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        rb_assert!(
            ruby,
            "!Time.respond_to?(:find_timezone, true) && \
             !JiffTimezone.respond_to?(:find_timezone)"
        );
        ruby.eval::<Value>("Object.send(:remove_const, :JiffTimezone)")?;
        let compatible = RClass::new(JiffTimeZone::class(ruby))?;
        ruby.class_object().const_set("JiffTimezone", compatible)?;
        ruby.eval::<Value>("ENV['JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION'] = 'false'")?;
        init(ruby)?;
        // Repeated init calls exercise cached validation and verify idempotency.
        init(ruby)?;
        ruby.eval::<Value>("ENV.delete('JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION')")?;
        init(ruby)?;
        rb_assert!(
            ruby,
            "JiffTimezone.equal?(compatible) && \
             !JiffTimezone.respond_to?(:find_timezone) && \
             !Time.respond_to?(:find_timezone, true)",
            compatible,
        );
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').instance_of?(JiffTimezone)");
        ruby.eval::<Value>("Object.send(:remove_const, :JiffTimezone)")?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        Ok(())
    });
}

#[test]
fn inherited_timezone_class_is_reused() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        let compatible = RClass::new(JiffTimeZone::class(ruby))?;
        let kernel = ruby.module_kernel();
        kernel.const_set("JiffTimezone", compatible)?;
        init(ruby)?;
        init(ruby)?;
        register(ruby)?;
        rb_assert!(
            ruby,
            "!Object.const_defined?(:JiffTimezone, false) && \
             JiffTimezone.equal?(compatible) && \
             Time.find_timezone('UTC').instance_of?(compatible)",
            compatible,
        );
        let time = jiff::ZonedDateTime::new(
            jiff::Timestamp::UNIX_EPOCH,
            jiff::tz::TimeZone::get("Asia/Tokyo").unwrap(),
        );
        rb_assert!(
            ruby,
            "time.zone.instance_of?(compatible) && time.utc_offset == 32400",
            time,
            compatible,
        );
        kernel.remove_const::<_, Value>("JiffTimezone")?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        Ok(())
    });
}

#[test]
fn foreign_resolver_is_preserved() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.eval::<Value>("def Time.find_timezone(name); [:foreign, name]; end")?;
        init(ruby)?;
        // The cached initialization path must preserve the application's resolver.
        init(ruby)?;
        rb_assert!(
            ruby,
            "Time.find_timezone('UTC') == [:foreign, 'UTC'] && \
             JiffTimezone.utc.iana_name == 'UTC'"
        );
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        // A foreign replacement after initialization must not be overwritten.
        ruby.eval::<Value>("def Time.find_timezone(name); :replacement; end")?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        rb_assert!(ruby, "Time.find_timezone('UTC') == :replacement");
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn compatible_class_and_resolver_are_reused() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        jiff_magnus::init(ruby)?;
        let class: Value = ruby.eval("JiffTimezone")?;
        let resolver: Value = ruby.eval("Time.method(:find_timezone)")?;
        let original: Value = ruby.eval("Time.find_timezone('America/New_York')")?;

        ruby.eval::<Value>(
            "def Time.method(name); \
             raise 'resolver lookup failed' if name.to_s == 'find_timezone'; super; end",
        )?;
        let error = second_provider::init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :method; end")?;
        rb_assert!(
            ruby,
            "JiffTimezone.equal?(original_class) && \
             Time.method(:find_timezone) == original_resolver",
            original_class = class,
            original_resolver = resolver,
        );

        second_provider::init(ruby)?;
        second_provider::init(ruby)?;
        jiff_magnus::init(ruby)?;
        rb_assert!(
            ruby,
            "JiffTimezone.equal?(original_class) && \
             Time.method(:find_timezone) == original_resolver && \
             zone.name == 'America/New_York' && zone.class == JiffTimezone && \
             Time.at(0, in: zone).utc_offset == -18000 && \
             Time.find_timezone('Asia/Tokyo').name == 'Asia/Tokyo'",
            original_class = class,
            original_resolver = resolver,
            zone = original,
        );
        let time: Time = magnus::eval!(ruby, "Time.at(0, in: zone)", zone = original)?;
        let zoned = jiff::ZonedDateTime::try_convert(time.as_value())?;
        assert_eq!(zoned.time_zone().iana_name(), Some("America/New_York"));

        ruby.eval::<Value>(
            "class << Time; remove_method :find_timezone; end; \
             def Time.singleton_method_added(name); \
             raise 'resolver hook failed' if name == :find_timezone; end",
        )?;
        let error = third_provider::init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(
            ruby,
            "JiffTimezone.equal?(original_class) && \
             JiffTimezone.utc.frozen? && !Time.respond_to?(:find_timezone, true)",
            original_class = class,
        );

        third_provider::init(ruby)?;
        third_provider::init(ruby)?;
        rb_assert!(
            ruby,
            "JiffTimezone.equal?(original_class) && \
             Time.find_timezone('Asia/Tokyo').instance_of?(JiffTimezone)",
            original_class = class,
        );
        Ok(())
    });
}

#[test]
fn failed_resolver_installation_does_not_publish_the_class() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.eval::<Value>("Time.freeze")?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_frozen_error()), "{error}");
        rb_assert!(
            ruby,
            "!Object.const_defined?(:JiffTimezone, false) && \
             !Time.respond_to?(:find_timezone, true)"
        );
        Ok(())
    });
}

#[test]
fn failed_registration_restores_existing_resolver_visibility() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        let time = ruby.class_time();
        for access in [Some("public"), Some("protected"), Some("private"), None] {
            if let Some(access) = access {
                ruby.eval::<Value>("def Time.find_timezone(name); :original; end")?;
                time.singleton_class()?
                    .funcall::<_, _, Value>(access, ("find_timezone",))?;
            } else {
                ruby.eval::<Value>(
                    "class << Time; remove_method :find_timezone; end; \
                     def Object.find_timezone(name); :original; end",
                )?;
            }
            let original: Value = time.funcall("method", ("find_timezone",))?;
            ruby.eval::<Value>(
                "def Time.singleton_method_added(name); \
                 raise 'registration failed' if name == :find_timezone; end",
            )?;
            let error = register(ruby).unwrap_err();
            assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
            ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
            rb_assert!(ruby, "Time.method(:find_timezone) == original", original);
            if let Some(access) = access {
                let visible: bool = time.singleton_class()?.funcall(
                    format!("{access}_method_defined?"),
                    ("find_timezone", false),
                )?;
                assert!(visible, "restored lookup lost {access} visibility");
            }
        }
        register(ruby)?;
        init(ruby)?;
        let original: Value = time.funcall("method", ("find_timezone",))?;
        time.freeze();
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_frozen_error()), "{error}");
        rb_assert!(ruby, "Time.method(:find_timezone) == original", original);
        Ok(())
    });
}

#[test]
fn rollback_preserves_resolvers_installed_by_removal_hooks() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        for initialized in [false, true] {
            if initialized {
                init(ruby)?;
            }
            for visibility in ["public", "protected", "private"] {
                if initialized {
                    ruby.eval::<Value>("def Time.find_timezone(name); :original; end")?;
                }
                ruby.eval::<Value>(&format!(
                    "Time.instance_variable_set(:@fail_once, true); \
                     def Time.singleton_method_added(name); \
                     return unless name == :find_timezone && @fail_once; \
                     @fail_once = false; raise 'installation failed'; end; \
                     def Time.singleton_method_removed(name); \
                     return unless name == :find_timezone; \
                     define_singleton_method(:find_timezone) {{ |_| :application }}; \
                     singleton_class.send(:{visibility}, :find_timezone); end"
                ))?;
                let error = if initialized {
                    register(ruby)
                } else {
                    init(ruby)
                }
                .unwrap_err();
                assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
                assert!(error.to_string().contains("installation failed"), "{error}");
                ruby.eval::<Value>(
                    "class << Time; \
                     remove_method :singleton_method_added; \
                     remove_method :singleton_method_removed; end",
                )?;
                rb_assert!(
                    ruby,
                    "Time.send(:find_timezone, 'UTC') == :application && \
                     Time.singleton_class.send(visibility, :find_timezone, false)",
                    visibility = format!("{visibility}_method_defined?"),
                );
                if !initialized {
                    rb_assert!(ruby, "!Object.const_defined?(:JiffTimezone, false)");
                }
                ruby.eval::<Value>("class << Time; remove_method :find_timezone; end")?;
            }
        }
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn rollback_preserves_visibility_changed_by_restoration_hooks() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.eval::<Value>(
            "def Time.find_timezone(name); :original; end; \
             Time.instance_variable_set(:@fail_once, true); \
             def Time.singleton_method_added(name); \
             return unless name == :find_timezone; \
             if @fail_once; @fail_once = false; raise 'installation failed'; \
             elsif !@replaced; @replaced = true; \
             define_singleton_method(:find_timezone) { |_| :application }; \
             singleton_class.send(:private, :find_timezone); end; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(
            ruby,
            "Time.send(:find_timezone, 'UTC') == :application && \
             Time.singleton_class.private_method_defined?(:find_timezone, false)"
        );
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn failed_registration_preserves_generated_resolver_with_matching_source() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.eval::<Value>(
            "def Time.singleton_method_added(name); \
             return unless name == :find_timezone && !@replacing; \
             @replacing = true; file, line = method(name).source_location; \
             singleton_class.class_eval( \
             'def find_timezone(name); :application; end', file, line); \
             raise 'installation failed'; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(ruby, "Time.find_timezone('UTC') == :application");
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn failed_registration_preserves_a_restored_native_resolver() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "Time.instance_variable_set(:@original_lookup, Time.method(:find_timezone)); \
             def Time.singleton_method_added(name); \
             return unless name == :find_timezone && !@replaced; \
             @replaced = true; \
             singleton_class.send(:define_method, :find_timezone, @original_lookup); \
             singleton_class.send(:private, :find_timezone); \
             raise 'installation failed'; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(
            ruby,
            "Time.method(:find_timezone) == original && \
             Time.singleton_class.private_method_defined?(:find_timezone, false) && \
             Time.send(:find_timezone, 'UTC').iana_name == 'UTC'",
            original,
        );
        init(ruby)?;
        register(ruby)?;
        rb_assert!(ruby, "Time.respond_to?(:find_timezone)");
        Ok(())
    });
}

#[test]
fn registration_does_not_require_vm_introspection() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.class_object().remove_const::<_, Value>("RubyVM")?;
        init(ruby)?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "Time.define_singleton_method(:singleton_method_added) do |name|; \
             raise 'installation failed' if name == :find_timezone; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        let restored: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        assert!(restored.funcall::<_, _, bool>("==", (original,))?);
        init(ruby)?;
        register(ruby)?;
        init(ruby)?;
        assert_eq!(
            ruby.eval::<String>("Time.find_timezone('UTC').iana_name")?,
            "UTC",
        );
        Ok(())
    });
}

#[test]
fn registration_rolls_back_when_called_from_a_tracepoint() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.define_global_function("register_jiff", magnus::function!(register, 0))?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "def Time.singleton_method_added(name); \
             raise 'installation failed' if name == :find_timezone; end",
        )?;
        ruby.eval::<Value>(
            "error = nil; trace = TracePoint.new(:line) do |event|; \
             event.disable; begin; register_jiff; rescue => raised; error = raised; end; end; \
             trace.enable { nil }; raise 'hook did not run' unless error&.message == 'installation failed'",
        )?;
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(ruby, "Time.method(:find_timezone) == original", original);
        init(ruby)?;
        Ok(())
    });
}

#[test]
fn registration_rejects_hooks_that_precede_rollback_tracking() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "Time.singleton_class.prepend(Module.new do; \
             def singleton_method_added(name); \
             raise 'hook failed' if name == :find_timezone; end; end)",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        assert!(error.to_string().contains("prepended"), "{error}");
        rb_assert!(ruby, "Time.method(:find_timezone) == original", original);
        init(ruby)?;
        Ok(())
    });
}

#[test]
fn rollback_preserves_application_resolvers_below_prepended_methods() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.eval::<Value>(
            "Time.singleton_class.prepend(Module.new do; \
             def find_timezone(name); super; end; end); \
             def Time.singleton_method_added(name); \
             raise 'installation failed' if name == :find_timezone; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        ruby.eval::<Value>(
            "def Time.singleton_method_added(name); \
             return unless name == :find_timezone && !@replaced; \
             @replaced = true; define_singleton_method(:find_timezone) { |_| :application }; \
             raise 'installation failed'; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(ruby, "Time.find_timezone('UTC') == :application");
        register(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn rollback_preserves_visibility_only_changes_from_restoration_hooks() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.eval::<Value>(
            "def Time.find_timezone(name); :original; end; \
             Time.singleton_class.send(:private, :find_timezone); \
             Time.instance_variable_set(:@fail_once, true); \
             def Time.singleton_method_added(name); \
             return unless name == :find_timezone; \
             if @fail_once; @fail_once = false; raise 'installation failed'; end; \
             singleton_class.send(:protected, :find_timezone); end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(
            ruby,
            "Time.send(:find_timezone, 'UTC') == :original && \
             Time.singleton_class.protected_method_defined?(:find_timezone, false)",
        );
        register(ruby)?;
        init(ruby)?;
        Ok(())
    });
}

#[test]
fn rollback_restores_resolvers_when_removal_hooks_change_method_hooks() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        ruby.eval::<Value>("Time.singleton_class.send(:private, :find_timezone)")?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "def Time.singleton_method_added(name); \
             raise 'installation failed' if name == :find_timezone; end; \
             def Time.singleton_method_removed(name); \
             return unless name == :find_timezone; \
             singleton_class.prepend(Module.new do; \
             def singleton_method_added(name); end; end); end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        rb_assert!(
            ruby,
            "Time.method(:find_timezone) == original && \
             Time.singleton_class.private_method_defined?(:find_timezone, false)",
            original,
        );
        init(ruby)?;
        Ok(())
    });
}

#[test]
fn repeated_registration_does_not_accumulate_symbols_or_ancestors() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        init(ruby)?;
        for _ in 0..5 {
            register(ruby)?;
        }
        let ancestors: usize = ruby.eval("Time.singleton_class.ancestors.length")?;
        let before: usize = ruby
            .eval("GC.start(full_mark: true, immediate_sweep: true); Symbol.all_symbols.length")?;
        for _ in 0..200 {
            register(ruby)?;
        }
        let after: usize = ruby
            .eval("GC.start(full_mark: true, immediate_sweep: true); Symbol.all_symbols.length")?;
        assert!(
            after <= before,
            "registration retained {} additional symbols",
            after.saturating_sub(before),
        );
        assert_eq!(
            ruby.eval::<usize>("Time.singleton_class.ancestors.length")?,
            ancestors,
        );
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn class_publication_preserves_application_lookup_on_failure_and_retry() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        if !ruby.class_object().respond_to("const_added", true)? {
            return Ok(());
        }
        ruby.eval::<Value>(
            "Object.instance_variable_set(:@fail_publication, true); \
             def Object.const_added(name); \
             return unless name == :JiffTimezone; \
             def Time.find_timezone(name); [:application, name]; end; \
             Time.singleton_class.send(:private, :find_timezone); \
             Time.instance_variable_set(:@application_lookup, Time.method(:find_timezone)); \
             raise 'publication failed' if @fail_publication; end",
        )?;
        let error = init(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
        assert!(error.to_string().contains("publication failed"), "{error}");
        rb_assert!(
            ruby,
            "!Object.const_defined?(:JiffTimezone, false) && \
             Time.method(:find_timezone) == Time.instance_variable_get(:@application_lookup) && \
             Time.send(:find_timezone, 'UTC') == [:application, 'UTC'] && \
             !Time.respond_to?(:find_timezone)"
        );
        ruby.eval::<Value>(
            "Object.instance_variable_set(:@fail_publication, false); \
             Time.singleton_class.send(:remove_method, :find_timezone)",
        )?;
        init(ruby)?;
        ruby.eval::<Value>("class << Object; remove_method :const_added; end")?;
        init(ruby)?;
        rb_assert!(
            ruby,
            "Time.method(:find_timezone) == Time.instance_variable_get(:@application_lookup) && \
             !Time.respond_to?(:find_timezone) && JiffTimezone.utc.iana_name == 'UTC'"
        );
        register(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn initialization_rejects_class_changes_from_hooks() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.eval::<Value>("ApplicationTimezone = Class.new")?;
        for hook in ["const_added", "singleton_method_added"] {
            if hook == "const_added" && !ruby.class_object().respond_to("const_added", true)? {
                continue;
            }
            let receiver = if hook == "const_added" {
                "Object"
            } else {
                "Time"
            };
            let watched = if hook == "const_added" {
                "JiffTimezone"
            } else {
                "find_timezone"
            };
            for replace in [false, true] {
                let replacement = if replace {
                    "Object.const_set(:JiffTimezone, ApplicationTimezone)"
                } else {
                    "nil"
                };
                ruby.eval::<Value>(&format!(
                    "{receiver}.instance_variable_set(:@changed, false); \
                     def {receiver}.{hook}(name); \
                     return unless name == :{watched} && !@changed; \
                     @changed = true; Object.send(:remove_const, :JiffTimezone); \
                     {replacement}; end"
                ))?;
                let error = init(ruby).unwrap_err();
                assert!(
                    error.is_kind_of(ruby.exception_load_error()),
                    "{hook}: {error}"
                );
                ruby.eval::<Value>(&format!("class << {receiver}; remove_method :{hook}; end"))?;
                assert!(!ruby.class_time().respond_to("find_timezone", true)?);
                if replace {
                    rb_assert!(ruby, "JiffTimezone.equal?(ApplicationTimezone)");
                    ruby.eval::<Value>("Object.send(:remove_const, :JiffTimezone)")?;
                } else {
                    rb_assert!(ruby, "!Object.const_defined?(:JiffTimezone, false)");
                }
            }
        }
        init(ruby)?;
        init(ruby)?;
        rb_assert!(ruby, "Time.find_timezone('UTC').iana_name == 'UTC'");
        Ok(())
    });
}

#[test]
fn initialization_can_retry_after_ruby_hook_errors() {
    with_fresh_ruby(|ruby| -> Result<(), Error> {
        ruby.define_global_function("reinitialize_jiff", magnus::function!(init, 0))?;
        ruby.eval::<Value>(
            "def Object.find_timezone(name); :inherited; end; \
             Time.singleton_class.send(:undef_method, :find_timezone)",
        )?;
        for callback in ["reinitialize_jiff", "JiffTimezone.register"] {
            ruby.eval::<Value>(&format!(
                "Time.instance_variable_set(:@reentered, false); \
                 def Time.singleton_method_added(name); \
                 return unless name == :find_timezone && !@reentered; \
                 @reentered = true; {callback}; end"
            ))?;
            let error = init(ruby).unwrap_err();
            assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
            assert!(error.to_string().contains("already in progress"), "{error}");
            ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
            rb_assert!(
                ruby,
                "!Object.const_defined?(:JiffTimezone, false) && \
                 !Time.respond_to?(:find_timezone, true)"
            );
        }

        for (setup, cleanup, message) in [
            (
                "def Time.singleton_method_added(name); \
                 raise 'resolver hook failed' if name == :find_timezone; end",
                "class << Time; remove_method :singleton_method_added; end",
                "resolver hook failed",
            ),
            (
                "def Time.method(name); \
                 raise 'resolver lookup failed' if name.to_s == 'find_timezone'; super; end",
                "class << Time; remove_method :method; end",
                "resolver lookup failed",
            ),
        ] {
            ruby.eval::<Value>(setup)?;
            let error = init(ruby).unwrap_err();
            assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
            assert!(error.to_string().contains(message), "{error}");
            ruby.eval::<Value>(cleanup)?;
            rb_assert!(
                ruby,
                "!Object.const_defined?(:JiffTimezone, false) && \
                 !Time.respond_to?(:find_timezone, true)"
            );
        }

        if ruby.class_object().respond_to("const_added", true)? {
            ruby.eval::<Value>(
                "def Object.const_added(name); \
                 raise 'class hook failed' if name == :JiffTimezone; end",
            )?;
            let error = init(ruby).unwrap_err();
            assert!(error.is_kind_of(ruby.exception_runtime_error()), "{error}");
            assert!(error.to_string().contains("class hook failed"), "{error}");
            ruby.eval::<Value>("class << Object; remove_method :const_added; end")?;
            rb_assert!(
                ruby,
                "!Object.const_defined?(:JiffTimezone, false) && \
                 !Time.respond_to?(:find_timezone, true)"
            );
        }

        init(ruby)?;
        init(ruby)?;
        let original: Value = ruby.class_time().funcall("method", ("find_timezone",))?;
        ruby.eval::<Value>(
            "Time.instance_variable_set(:@reentered, false); \
             def Time.singleton_method_added(name); \
             return unless name == :find_timezone && !@reentered; \
             @reentered = true; JiffTimezone.register; end",
        )?;
        let error = register(ruby).unwrap_err();
        assert!(error.is_kind_of(ruby.exception_load_error()), "{error}");
        ruby.eval::<Value>("class << Time; remove_method :singleton_method_added; end")?;
        rb_assert!(ruby, "Time.method(:find_timezone) == original", original);
        register(ruby)?;
        init(ruby)?;
        rb_assert!(
            ruby,
            "Time.find_timezone('America/New_York').instance_of?(JiffTimezone) && \
             Time.at(0, in: 'Asia/Tokyo').utc_offset == 32400"
        );
        Ok(())
    });
}

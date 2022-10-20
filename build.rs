use std::env;

const RUBY_VERSIONS: [(u8, u8); 4] = [(2, 7), (3, 0), (3, 1), (3, 2)];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("cargo:rerun-if-env-changed=RUBY");
    println!("cargo:rerun-if-env-changed=RUBY_VERSION");

    configure_libruby();

    let major = dep_rb_value("MAJOR").parse::<u8>()?;
    let minor = dep_rb_value("MINOR").parse::<u8>()?;

    let version = (major, minor);

    for &v in &RUBY_VERSIONS {
        if version < v {
            println!(r#"cargo:rustc-cfg=ruby_lt_{}_{}"#, v.0, v.1);
        }
        if version <= v {
            println!(r#"cargo:rustc-cfg=ruby_lte_{}_{}"#, v.0, v.1);
        }
        if version == v {
            println!(r#"cargo:rustc-cfg=ruby_{}_{}"#, v.0, v.1);
        }
        if version >= v {
            println!(r#"cargo:rustc-cfg=ruby_gte_{}_{}"#, v.0, v.1);
        }
        if version > v {
            println!(r#"cargo:rustc-cfg=ruby_gt_{}_{}"#, v.0, v.1);
        }
    }

    Ok(())
}

/// Setup libruby. Ideally, `rb-sys` linker flags could be inherited but that's
/// not currently possible with Cargo.
fn configure_libruby() {
    println!("cargo:rustc-link-search=native={}", dep_rb_value("LIBDIR"));
}

/// Gets a value from the rb-sys build output.
fn dep_rb_value(key: &str) -> String {
    let key = format!("DEP_RB_{}", key);
    println!("cargo:rerun-if-env-changed={}", key);
    env::var(key).unwrap().to_string()
}

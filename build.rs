use std::env;

const RUBY_VERSIONS: [(u8, u8); 4] = [(2, 7), (3, 0), (3, 1), (3, 2)];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("cargo:rerun-if-env-changed=RUBY");
    println!("cargo:rerun-if-env-changed=RUBY_VERSION");

    let major = dep_rb_value("DEP_RB_MAJOR").parse::<u8>()?;
    let minor = dep_rb_value("DEP_RB_MINOR").parse::<u8>()?;
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

fn dep_rb_value(key: &str) -> String {
    env::var_os(key).unwrap().to_string_lossy().to_string()
}

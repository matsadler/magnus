fn main() -> Result<(), Box<dyn std::error::Error>> {
    // add these here to silence warnings until rb_sys_env is updated
    println!("cargo:rustc-check-cfg=cfg(ruby_use_flonum)");
    println!("cargo:rustc-check-cfg=cfg(ruby_lt_3_0)");
    println!("cargo:rustc-check-cfg=cfg(ruby_gte_3_0)");
    println!("cargo:rustc-check-cfg=cfg(ruby_gte_3_1)");
    println!("cargo:rustc-check-cfg=cfg(ruby_lt_3_2)");
    println!("cargo:rustc-check-cfg=cfg(ruby_gte_3_2)");
    println!("cargo:rustc-check-cfg=cfg(ruby_lt_3_3)");
    println!("cargo:rustc-check-cfg=cfg(ruby_gte_3_3)");

    let _ = rb_sys_env::activate()?;

    Ok(())
}

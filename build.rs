use std::{
    collections::HashMap,
    env,
    error::Error,
    ffi::OsStr,
    fmt,
    path::{Path, PathBuf},
    process::Command,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rbconfig = RbConfig::new()?;

    match (rbconfig.get("RUBY_SO_NAME"), rbconfig.get("LIBRUBY_A")) {
        (Ok(_), Ok(_)) if env::var_os("RUBY_STATIC").is_some() => use_static(&rbconfig)?,
        (Ok(libruby_so), _) => println!("cargo:rustc-link-lib=dylib={}", libruby_so),
        (Err(_), Ok(_)) => use_static(&rbconfig)?,
        (Err(e), _) => return Err(e.into()),
    }

    println!("cargo:rustc-link-search={}", rbconfig.get("libdir")?);

    if !is_command("llvm-config") && is_command("brew") {
        let output = Command::new("brew").arg("--prefix").output()?;
        let prefix = String::from_utf8(output.stdout)?;
        let path = Path::new(&prefix).join("opt/llvm/bin/llvm-config");
        std::env::set_var("LLVM_CONFIG_PATH", path);
    }

    let mut builder = bindgen::Builder::default()
        .header("ruby_sys.h")
        .clang_arg(format!("-I{}", rbconfig.get("rubyhdrdir")?))
        .clang_arg(format!("-I{}", rbconfig.get("rubyarchhdrdir")?));
    for key in &[
        "sitehdrdir",
        "vendorhdrdir",
        "sitearchhdrdir",
        "vendorarchhdrdir",
    ] {
        if let Ok(path) = rbconfig.get(*key) {
            builder = builder.clang_arg(format!("-I{}", path));
        }
    }
    if let Ok(cc) = rbconfig.get("CC") {
        if cc.contains("-fdeclspec") {
            builder = builder.clang_arg("-fdeclspec");
        }
    }
    let bindings = builder
        .allowlist_function("rb_.*")
        .allowlist_function("ruby_.*")
        .allowlist_type("ruby_.*")
        .allowlist_type("R[A-Z].*")
        .allowlist_type("rbimpl_typeddata_flags")
        .allowlist_var("rb_.*")
        .default_enum_style(bindgen::EnumVariation::Rust {
            non_exhaustive: false,
        })
        .no_copy("rb_data_type_struct")
        .layout_tests(false)
        .generate_comments(false)
        .generate()
        .map_err(|_| BindingError())?;

    let out_path = PathBuf::from(env::var("OUT_DIR")?);
    bindings.write_to_file(out_path.join("ruby_sys.rs"))?;
    Ok(())
}

fn use_static(rbconfig: &RbConfig) -> Result<(), RbConfigMissing> {
    let libs = rbconfig.get("LIBS")?;
    println!("cargo:rustc-link-lib=static=ruby-static");
    println!("cargo:rustc-flags={}", libs.replace("-l", "-l "));
    Ok(())
}

struct RbConfig(HashMap<String, String>);

impl RbConfig {
    fn new() -> Result<Self, RbConfigError> {
        let ruby = match env::var_os("RUBY") {
            Some(val) => val,
            None => OsStr::new("ruby").to_os_string(),
        };
        let output = Command::new(ruby)
            .arg("-e")
            .arg("print RbConfig::CONFIG.map {|kv| kv.join(\"\x1F\")}.join(\"\x1E\")")
            .output()?;
        let config = String::from_utf8(output.stdout)?;

        let mut res = HashMap::new();
        for line in config.split('\x1E') {
            if let Some((key, val)) = line.split_once('\x1F') {
                if !val.is_empty() {
                    res.insert(key.to_owned(), val.to_owned());
                }
            }
        }
        Ok(RbConfig(res))
    }

    fn get(&self, key: &str) -> Result<&str, RbConfigMissing> {
        self.0
            .get(key)
            .map(|v| v.as_str())
            .ok_or_else(|| RbConfigMissing(key.to_owned()))
    }
}

#[derive(Debug)]
enum RbConfigError {
    Io(std::io::Error),
    Utf8(std::string::FromUtf8Error),
}

impl fmt::Display for RbConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Utf8(e) => e.fmt(f),
        }
    }
}

impl Error for RbConfigError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            Self::Utf8(e) => Some(e),
        }
    }
}

impl From<std::io::Error> for RbConfigError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl From<std::string::FromUtf8Error> for RbConfigError {
    fn from(e: std::string::FromUtf8Error) -> Self {
        Self::Utf8(e)
    }
}

#[derive(Debug)]
struct RbConfigMissing(String);

impl fmt::Display for RbConfigMissing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Couldn't find {:?} in RbConfig", self.0)
    }
}

impl Error for RbConfigMissing {}

#[derive(Debug)]
struct BindingError();

impl fmt::Display for BindingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to build bindings")
    }
}

impl Error for BindingError {}

fn is_command(name: &str) -> bool {
    let exts = env::var_os("PATHEXT")
        .map(|s| env::split_paths(&s).collect::<Vec<_>>())
        .unwrap_or_else(|| vec![PathBuf::new()]);
    let path = match env::var_os("PATH") {
        Some(v) => v,
        None => return false,
    };
    env::split_paths(&path).any(|p| {
        exts.iter().any(|ext| {
            let mut exe = PathBuf::new();
            exe.push(name);
            exe.push(ext);
            is_executable(&Path::new(&p).join(exe))
        })
    })
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;

    let meta = match std::fs::metadata(path) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let is_executable = meta.permissions().mode() & 0o111 != 0;
    is_executable && !meta.is_dir()
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    !path.is_dir()
}

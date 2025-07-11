//! Types and functions for working with Ruby IO semantics in Rust.
//!
//! This module provides safe wrappers and accessors for working with Ruby's IO system,
//! including file open flags (`OpenFlags`), mode flags (`FMode`), and encoding metadata
//! (`IoEncoding`).

#[cfg(ruby_lt_3_3)]
use rb_sys::rb_io_enc_t as rb_io_encoding;
#[cfg(ruby_gt_3_4)]
use rb_sys::rb_io_mode;
#[cfg(ruby_gte_3_3)]
use rb_sys::{rb_io_encoding, FMODE_EXTERNAL};
use rb_sys::{
    rb_io_extract_modeenc, OnigEncodingTypeST, FMODE_APPEND, FMODE_BINMODE, FMODE_CREATE,
    FMODE_DUPLEX, FMODE_EXCL, FMODE_READABLE, FMODE_READWRITE, FMODE_SETENC_BY_BOM, FMODE_SYNC,
    FMODE_TEXTMODE, FMODE_TRUNC, FMODE_TTY, FMODE_WRITABLE, VALUE,
};

use crate::{
    encoding::{Encoding, RbEncoding},
    error::{protect, Error},
    value::{private::ReprValue as _, ReprValue, Value},
    RHash, Ruby,
};

/// Wrapper for Ruby's file open flag bits (`O_*`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpenFlags(pub i32);

impl OpenFlags {
    /// Constructs a new set of open flags.
    pub fn new(bits: i32) -> Self {
        Self(bits)
    }

    /// Returns the raw flag bits.
    pub fn bits(&self) -> i32 {
        self.0
    }

    /// Checks if a particular flag is set.
    pub fn contains(&self, flag: i32) -> bool {
        self.0 & flag != 0
    }
}

/// Ruby IO mode flags (`FMODE_*`), used to describe how a file or stream is opened.
///
/// These are internal Ruby VM flags describing the open mode and encoding behavior
/// of an IO stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FMode(u32);

#[cfg(ruby_lt_3_3)]
const FMODE_EXTERNAL: u32 = 65536; // this was FMODE_PREP. rb-sys doesn't include this binding.

impl FMode {
    /// File is opened as readable (`"r"`, `"r+"`, etc.)
    pub const READ: u32 = FMODE_READABLE;
    /// File is opened as writable (`"w"`, `"a"`, `"r+"`, etc.)
    pub const WRITE: u32 = FMODE_WRITABLE;
    /// File is readable and writable (`"r+"`, `"w+"`, etc.)
    pub const READ_WRITE: u32 = FMODE_READWRITE;
    /// File is opened in binary mode (`"b"` modifier)
    ///
    /// Disables newline conversions and sets default external encoding to ASCII-8BIT.
    pub const BINARY_MODE: u32 = FMODE_BINMODE;
    /// File is opened with sync mode (`IO#sync = true`)
    pub const SYNC: u32 = FMODE_SYNC;
    /// The stream is connected to a terminal/TTY
    pub const TTY: u32 = FMODE_TTY;
    /// Duplex stream — supports both input and output on a single handle
    pub const DUPLEX: u32 = FMODE_DUPLEX;
    /// Append mode — all writes go to the end of the file
    pub const APPEND: u32 = FMODE_APPEND;
    /// Create mode — file is created if it doesn't exist
    pub const CREATE: u32 = FMODE_CREATE;
    /// Exclusive mode — fail if file exists
    pub const EXCLUSIVE: u32 = FMODE_EXCL;
    /// Truncate the file to 0 bytes on open
    pub const TRUNCATE: u32 = FMODE_TRUNC;
    /// File is opened in text mode (`"t"` modifier)
    ///
    /// Affects encoding and newline translation on some platforms.
    pub const TEXT_MODE: u32 = FMODE_TEXTMODE;
    /// External encoding explicitly specified
    pub const EXTERNAL_ENCODING: u32 = FMODE_EXTERNAL;
    /// Set encoding by inspecting BOM (Byte Order Mark)
    pub const BOM_ENCODING: u32 = FMODE_SETENC_BY_BOM;

    /// Constructs a new `FMode` from raw bits.
    pub fn new(bits: u32) -> Self {
        Self(bits)
    }

    /// Check if a given flag is set.
    pub fn contains(&self, flag: u32) -> bool {
        self.0 & flag != 0
    }

    /// Returns the raw flag bits.
    pub fn bits(&self) -> u32 {
        self.0
    }
}

/// Ruby-owned encoding metadata extracted from IO options.
///
/// This struct represents the result of parsing Ruby's file mode string and encoding-related
/// options (e.g., `:external_encoding`, `:internal_encoding`, or `:encoding`) using the
/// internal Ruby C API `rb_io_extract_modeenc`.
///
/// The data here includes both Ruby-side encodings and flags that affect transcoding behavior,
/// such as BOM handling or newline modes. The optional `options` hash contains additional
/// transcoding options as a Ruby `Hash`.
///
/// # Example
///
/// ```rust
/// # use magnus::{Ruby, Value, RHash};
/// # fn parse_encoding(ruby: &Ruby, mode: &mut Value, perm: &mut Value, options: &RHash) {
/// let (_, _, encoding) = ruby.io_extract_modeenc(mode, perm, options).unwrap();
///
/// if let Some(ext) = &encoding.external {
///     println!("External encoding: {}", ext);
/// }
///
/// if let Some(hash) = &encoding.options {
///     println!("Encoding options: {:?}", hash);
/// }
/// # }
/// ```
///
/// # Safety
///
/// This struct should **not be stored beyond the stack frame** in which it was created.
/// The Ruby VM may deallocate or reuse internal objects such as the `options` hash,
/// which is **not automatically GC-pinned**. Copying this structure beyond a single
/// call boundary can lead to undefined behavior or use-after-free.
///
/// Always extract the fields you need and clone or persist Ruby values separately if necessary.
pub struct IoEncoding {
    /// The external encoding used for reading/writing to the file or stream.
    pub external: Option<Encoding>,
    /// The internal encoding used for transcoding, if any.
    pub internal: Option<Encoding>,
    /// Encoding flags describing transcoding behavior (e.g., whether to
    /// use BOM detection, or newline modes).
    pub flags: i32,
    /// A Ruby hash of encoding options passed in by the user, if present.
    pub options: Option<RHash>,
}

/// # IO helper functions
///
/// See also [`IoEncoding`] type and [`FMode`] type.
impl Ruby {
    /// Extract open flags and IO encoding metadata from a Ruby method call.
    ///
    /// This wraps Ruby's `rb_io_extract_modeenc` function, which parses `mode`, `perm`, and `options`
    /// into a combination of open flags, mode flags, and encoding metadata.
    ///
    /// Can raise:
    /// - `TypeError` if passed unexpected objects (e.g., `Time`)
    /// - `ArgError` if conflicting options are provided
    pub fn io_extract_modeenc(
        &self,
        mode: &mut Value,
        permission: &mut Value,
        option: &RHash,
    ) -> Result<(OpenFlags, FMode, IoEncoding), Error> {
        // `rb_io_extract_modeenc` will fill these variables:
        let mut oflags: std::os::raw::c_int = 0; // with O_ flags; flags are available in `File::Constants`.
        #[cfg(ruby_lte_3_4)]
        let mut fmode: std::os::raw::c_int = 0; // with FMODE_ flags
        #[cfg(ruby_gt_3_4)]
        let mut fmode: rb_io_mode = rb_io_mode::RUBY_IO_MODE_EXTERNAL; // arbitrary initialization value
        let mut io_encoding: rb_io_encoding = unsafe { std::mem::zeroed() }; // with IO encoding options

        // Can raise:
        // - `TypeError`: Unexpected object (e.g. Time) passed.
        // - `ArgError`: Contradiction inside of params.
        protect(|| unsafe {
            rb_io_extract_modeenc(
                &mut mode.as_rb_value() as *mut _,
                &mut permission.as_rb_value() as *mut _,
                option.as_rb_value(),
                &mut oflags as *mut _,
                &mut fmode as *mut _,
                &mut io_encoding as *mut _,
            );
            self.qnil()
        })?;

        // `rb_io_extract_modeenc` populated the values
        let open_flags = OpenFlags::new(oflags as i32);
        let fmode_flags = FMode::new(fmode as u32);

        // extracts and starts to manage objects for better user experience
        let internal: Option<Encoding> = {
            let ptr = io_encoding.enc as *mut OnigEncodingTypeST;
            RbEncoding::new(ptr).map(|r| r.into())
        };

        let external: Option<Encoding> = {
            let ptr = io_encoding.enc2 as *mut OnigEncodingTypeST;
            RbEncoding::new(ptr).map(|r| r.into())
        };

        let flags = io_encoding.ecflags;

        let options = {
            let value = Value::new(io_encoding.ecopts as VALUE);
            if value.is_nil() {
                None
            } else {
                RHash::from_value(value)
            }
        };

        let io_encoding = IoEncoding {
            external,
            internal,
            flags,
            options,
        };

        Ok((open_flags, fmode_flags, io_encoding))
    }
}

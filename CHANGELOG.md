# Changelog

## [Unreleased]
### Added
- `Value::funcall_with_block`.
- impl `TryConvert` for `Exception` and `ExceptionClass`.
- `Class` trait (implemented for `RClass` and `ExceptionClass`).
- `define_error` and `Module::define_error` helpers for defining an Exception
  Class.
- `RTypedData::wrap` and `RTypedData::get` inherent methods for wrapping Rust
  types in Ruby objects.

### Changed
- Switched to rb-sys for low level bindings.
- Ruby types are no longer `Send` or `Sync`.
- Rust types wrapped in Ruby objects must be `Send`.
- Only function pointers (fn or non-capturing closure) are accepted as argument
  for `Value::block_call`. Use `Proc::from_fn` + `Value::funcall_with_block`
  for closures that capture variables.
- `Proc::new` only accepts a function pointer, use `Proc::from_fn` for closures
  that capture variables.
- `ExceptionClass::default()` now returns `StandardError` rather than
  `RuntimeError`.
- `TryConvert` now takes `Value` by value (rather than a reference).

### Deprecated

### Removed

### Fixed

### Security
- `printf`-style format strings no longer interpreted in error messages when
  automatically raised as Ruby exceptions.

## [0.3.2] - 2022-05-29

### Fixed
- Better error output from build script when `ruby` can't be found or errors.
- Fixed crash in `Proc::new` and `Value::block_call` when the proc was stored
  and called later.

## [0.3.1] - 2022-05-21

### Fixed
- Integer overflow in Ruby Float to f64 conversion

## [0.3.0] - 2022-05-18
### Added
- `RString::new_shared` and `RString::new_frozen`.
- `encoding` module, including `encoding::Index` and `RbEncoding` types.
- `RString::enc_coderange` and related methods.
- `RString::codepoints` and `RString::char_bytes` iterators over string
  contents.
- The following methods for `RArray`: `dup`, `concat`, `plus`, `delete`,
  `delete_at`, `resize`, `reverse`, `rotate`, and `sort`.
- New methods for `RString`: `enc_new`, `len`, `length`, and `is_empty`.
- `RHash` gains the methods `delete` and `clear`.
- `require`, `current_receiver`, `call_super`, and `define_global_const`
  functions.
- `Object::singleton_class` and `Object::extend_object`.
- `Proc::new`, `Proc::arity`, and `Proc::is_lambda`.
- `superclass` and `name` methods for `RClass`.
- `scan_args::check_arity`.
- Methods for `Module`: `include_module`, `prepend_module`, `const_set`,
  `ancestors`, `define_attr`, and `define_alias`.
- `rb-sys-interop` feature to use low level bindings from rb-sys, and `rb_sys`
  module to expose functions for working with rb-sys.
- Added `gc::register_mark_object`, `gc::register_address`,
  `gc::unregister_address`, `gc::count`, `gc::stat`, and `gc::all_stats`.
- `Error::iter_break`.
- `StaticSymbol::check` and `Id::check` to check if a symbol exists.

### Changed
- `RArray::cat`, `RArray::from_slice`, and `gc::mark_slice` will accept a
  slice of any Ruby type as an argument, rather than only a slice of `Value`.
  This may change type inference rules such that things like
  `RArray::from_slice(&[1.into()])` will no longer work. Use
  `RArray::from_slice(&[Value::from(1)])` instead.
- Similar to above, `gc::location` will accept any Ruby type as an argument.
- `BoxValue` can hold any Ruby type, not just `Value`.
- Improved performance for conversion between Ruby floats/integers and Rust
  types.
- The parameters to the closure passed to `RHash::foreach` will now be
  automatically converted from `Value` to Rust types.
- `Module::define_method`, `Module::define_private_method`,
  `Module::define_protected_method`, `RModule::define_singleton_method`, and
  `Object::define_singleton_method` all return `Result<(), Error>` rather than
  `()` as they may fail in the unusual case that the receiver is frozen.

### Deprecated
- `String::encode_utf8`, use `r_string.conv_enc(RbEncoding::utf8())` instead.
- `Value::leak`, use `gc::register_mark_object` instead.
- `define_global_variable` (use `define_variable`) to better match Ruby C API
  naming.

### Removed
- `error::protect` removed as it should not be needed when using Magnus. For
  use with rb-sys enable the `rb-sys-interop` feature and use
  `magnus::rb_sys::protect`.
- `Qfalse::new`, `Qnil::new`, `Qtrue::new`, `Qundef::new` (use
  QFALSE/QNIL/QTRUE/QUNDEF).
- Functions for generating an `Error` with a specific Ruby type. E.g.
  `Error::type_error("...")`, use `Error::new(exception::type_error(), "...")`.

### Fixed
- creating a `StaticSymbol` from a `&str` with characters outside the ASCII
  range.
- panicking in any of the functions of `DataTypeFunctions` will abort the
  process to avoid undefined behaviour.
- panicking in the closure passed to `RHash::foreach` won't result in undefined
  behaviour.

## [0.2.1] - 2022-04-03

### Fixed
- Fixed compilation error in `method!` and `function!` macros with arity
  argument of 5.

## [0.2.0] - 2022-03-31
### Added
- Functions in `class`, `module`, and `error` modules to access built-in
  classes/modules.
- Many doc examples.
- `RArray::len`, `RArray::includes`, `RArray::join`, `RArray::is_shared`,
  `RArray::replace`, and `RArray::subseq`.
- Implement `From<&str>` and `From<String>` for `RString`.
- Support for `Range`.
- Pre-built bindings for Ruby 3.1 on Windows.
- Support calling Ruby methods with Rust closure as a Ruby block.
- `Class::new` and `Module::new` for creating anonymous classes/modules.
- `r_string!` macro to create Ruby string from a `str` literal.
- `Value::equal` and `Value::eql` for object equality.
- `Value::respond_to` and `Value::check_funcall` for conditionally calling Ruby
  methods only when they are defined.
- `scan_args` and `get_kwargs` for complex argument parsing.

### Changed
- `Qundef::to_value` now marked `unsafe`.
- `RArray::cat`, `RArray::push`, `RArray::unshift`, and `RArray::store` now
  return `Result<(), Error>`.
- `eval!` macro uses anonymous (rather than caller's) binding.

### Deprecated
- `Qfalse::new`, `Qnil::new`, `Qtrue::new`, `Qundef::new` (use
  QFALSE/QNIL/QTRUE/QUNDEF).
- Functions for generating an `Error` with a specific Ruby type. E.g.
  `Error::type_error("...")` is now `Error::new(exception::type_error(), "...")`
- `Binding::new`. This will be removed in the future as the underlying
  `rb_binding_new` will not function as of Ruby 3.2.

### Fixed
- Converting Ruby integers to `isize`/`i64`/`usize`/`u64` on Windows.
- Edge case where static symbol created after a dynamic symbol with the same
  name wouldn't be detected as static.
- Many `RArray` methods now correctly protect from exceptions (instead
  returning `Result<_, Error>` when an exception occurs).

## [0.1.0] - 2022-02-25
### Added
- Support for most core classes, `String`, `Symbol`, `Integer`, `Float`,
  `Array`, `Hash` and more.
- Defining Rust methods as Ruby functions.
- Calling Ruby methods from Rust.
- Automatic type conversion between Rust and Ruby types.
- Conversion from Ruby exceptions to Rust Results and visa versa.
- Support for wrapping custom Rust structs as Ruby objects.
- `Enumerator` as a iterator.
- `yield` to Ruby blocks.
- `#[init]` macro to mark init function to load extension with `require`.
- Pre-built bindings for Ruby 2.6 - 3.1 on common platforms, build-time
  generated bindings otherwise.

[Unreleased]: https://github.com/matsadler/magnus/compare/0.3.2...HEAD
[0.3.2]: https://github.com/matsadler/magnus/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/matsadler/magnus/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/matsadler/magnus/compare/0.2.1...0.3.0
[0.2.1]: https://github.com/matsadler/magnus/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/matsadler/magnus/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/matsadler/magnus/tree/0.1.0

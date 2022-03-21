# Changelog

## [Unreleased]
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

### Changed
- `Qundef::to_value` now marked `unsafe`.
- `RArray::cat`, `RArray::push`, `RArray::unshift`, and `RArray::store` now
  return `Result<(), Error>`.
- `eval!` macro uses anonymous (rather than caller's) binding.

### Deprecated

### Removed
- `Qfalse::new`, `Qnil::new`, `Qtrue::new`, `Qundef::new` (use
  QFALSE/QNIL/QTRUE/QUNDEF).
- Functions for generating an `Error` with a specific Ruby type. E.g.
  `Error::type_error("...")` is now `Error::new(exception::type_error(), "...")`

### Fixed
- Converting Ruby integers to `isize`/`i64`/`usize`/`u64` on Windows.
- Edge case where static symbol created after a dynamic symbol with the same
  name wouldn't be detected as static.
- Many `RArray` methods now correctly protect from exceptions (instead
  returning `Result<_, Error>` when an exception occurs).

### Security

## [0.1.0] - 22-01-25
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

[Unreleased] https://github.com/matsadler/magnus/compare/0.1.0...HEAD
[0.1.0]: https://github.com/matsadler/magnus/tree/0.1.0

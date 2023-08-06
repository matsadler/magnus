# Changelog

## [Unreleased]
### Added
- `Thread`, `Ruby::thread_create`/`thread_create_from_fn` and other thread APIs.
- `Ruby::ary_try_from_iter` is an efficient way to create a Ruby array from a
  fallible Rust iterator.
- `Ruby::hash_from_iter` and `Ruby::hash_try_from_iter`.

### Changed

### Deprecated

### Removed
- `deprecated-send-sync-value` feature.
- `ruby-static` feature. Instead enable the feature for `rb-sys` in your
  Cargo.toml like so: `rb-sys = { version = "*", features = ["ruby-static"] }`
- `typed_data::Obj::get`.
- The `QTRUE`, `QFALSE`, and `QNIL` constants.
- `Class::undef_alloc_func`.
- `Value::try_convert`.
- `Binding`.
- `gc::{mark, mark_slice, mark_movable, location}`.
- `RStruct::as_slice`.
- `Exception::backtrace`.

### Fixed

### Security

## [0.6.0] - 2023-07-28
### Added
- `value::Opaque` can be used to wrap a Ruby type to make it `Send` + `Sync`.
- `value::Lazy` lazily initialises a Ruby value so it can be assigned to a
  `static`.
- `value::OpaqueId` is a `Send` + `Sync` version of `value::Id`.
- `value::LazyId` is an `Id` with a `const` constructor so can be assigned to a
  `static` and derefs to `OpaqueId`.
- `error::OpaqueError` is a `Send` + `Sync` version of `Error`.
- The `#[magnus(opaque_attr_reader)]` attribute can be set on `Opaque` wrapped
  fields of a struct when deriving `TypedData` to generate a method to return
  the inner value.
- `Ruby::init` function to initialise Ruby when embedding Ruby in Rust that
  runs a function with Ruby initialised, passing `&Ruby`.
- `rb_assert!()` macro to assert a Ruby expression evaluates to a truthy value.
- `Class::undef_default_alloc_func` to remove a class' allocator function only
  if it is Ruby's default allocator function.
- `Class::obj_alloc` and `Class::define_alloc_func` for allocating an object
  without calling `initialize`, and for defining an allocator function.
- `RTypedData::wrap_as` & `typed_data::Obj<T>::wrap_as` can be used to
  dynamically set the class when wrapping Rust data in a Ruby object. This can
  be used to allow wrapped data to be subclassed in Ruby.
- `Exception::exception_class` returns the class of an exception as an
  `ExceptionClass`.
- The `kwargs!()` macro and `KwArgs` type can be used to pass keyword arguments
  to `ReprValue::funcall`, et al.

### Changed
- Minimum supported Rust version in now 1.61.
- The `bytes-crate` feature has been renamed to `bytes`.
- The `rb-sys-interop` feature has been renamed to `rb-sys`.
- Ruby types are no longer `Send` or `Sync`. These types can be made `Send` &
  `Sync` with the `deprecated-send-sync-value` feature. This feature is meant
  to ease upgrading and will be removed with the next release.
- `Value`'s methods moved to the `ReprValue` trait.
- `typed_data::Obj<T>` derefs to `T` so now `T`'s methods can be called
  directly on `typed_data::Obj<T>`.
- `ReprValue` and `TryConvert` added to `magnus::prelude`.
- `typed_data::Cmp`, `typed_data::Dup` and `typed_data::Inspect` traits to help
  with implementing `#<=>`, `#dup` & `#clone`, and `#inspect` methods for
  wrapped structs.
- Wrapped data must be `Sync` to enable `frozen_shareable` flag.
- `TypedData::class` and `TypedData::class_for` now take a `&Ruby` argument.
- `DataTypeFunctions::mark` and `DataTypeFunctions::compact` now take
  `&gc::Marker` and `&gc::Compactor` arguments respectively.
- Init function marked with `#[magnus::init]` optionally takes a `&Ruby`
  argument.
- Functions bound as Ruby methods with `method!()` and `function!()` optionally
  take `&Ruby` as a first argument.
- The value returned from `embed::init` derefs to `Ruby`.
- `DataTypeBuilder::new`/`DataType::builder` now take their `name` argument
  as a `'static CStr` (see the `magnus::data_type_builder!` macro to construct
  a `DataTypeBuilder` with a `'static CStr` `name`).
- All methods on `DataTypeBuilder` are now `const`, so `DataType` can be
  constructed in a `const` context and be assigned to a `static`.
- The `#[wrap]` and `#[derive(TypedData)]` macros now support setting the
  `#[magnus(unsafe_generics)]` attribute to allow deriving `TypedData` for
  types with generics. The derived implementation is not guaranteed to be
  correct.

### Deprecated
- `typed_data::Obj::get` as it is made redundant by the `Deref` implementation
  for `typed_data::Obj`.
- The `QTRUE`, `QFALSE`, and `QNIL` constants. Please use `value::qtrue()`,
  `value::qfalse()`, and `value::qnil()`.
- `Class::undef_alloc_func`. Please use `Class::undef_default_alloc_func`.
- `Value::try_convert`, prefer `TryConvert::try_convert` or `T::try_convert`.
- `Binding`. To call methods on Ruby's binding, use `ReprValue::funcall` on a
  `Value` know to be an instance of Ruby's Binding class.
- `gc::{mark, mark_slice, mark_movable, location}`, instead use
  `gc::Marker::{mark, mark_slice, mark_movable}` and `Compactor::location`.
- `RStruct::as_slice`.

### Removed
- Inherent methods on `RClass`, import `magnus::Class` trait or
  `magnus::prelude::*`.
- `Into<Value>`/`From<T> for Value` implementations, use `IntoValue`.
- `Default` implementations for `Value`, `RClass`, and `ExceptionClass`.
- `Error` can no longer be directly constructed, must use `Error::new` or
  `Error::from`/`Exception::into`.
- `RString::append` (use `RString::buf_append`).
- `Error::runtime_error` (use `Error::new(exception::runtime_error(), msg)`).

### Fixed
- `RFloat::from_value` now returns `None` when value is a `Flonum`.

## [0.5.3] - 2023-04-07
### Added
- `Value::as_value` method that can be called on any Ruby type (as all Ruby
  types deref to `Value`) as a forward-compatible way to convert a Ruby type to
  `Value`.

## [0.5.2] - 2023-03-19
### Fixed
- Fixed compilation issue in `RBignum` on 32 bit platforms.

## [0.5.1] - 2023-02-18
### Fixed
- Documentation fixes.

## [0.5.0] - 2023-02-11
### Added
- `typed_data::Obj<T>`, a Ruby object wrapping a Rust type known to be `T`.
- `RArray::to_ary`, `RArray::assoc`, `RArray::rassoc`, and `RArray::cmp`.
- `RHash::with_capacity` new for Ruby 3.2.
- `RHash::bulk_insert`.
- `Value::hash` to generate a hash key for a Ruby object.
- `typed_data::Hash` and `typed_data::IsEql` traits to help with implementing
  `#hash` and `#eql?` methods for wrapped structs.
- Lots of `RString` methods: `capacity`, `cmp`, `comparable`, `drop_bytes`,
  `dump`, `ellipsize`, `offset`, `plus`, `times`, `replace`, `scrub`,
  `shared_replace`, `split`, `update`.
- `RRegexp::new`/`new_str`, `RRegexp::reg_match`, and `RRegexp::options`.
- The `backref_get` function to get the `RMatch` for the last regexp match.
- `RMatch::nth_defined`, `RMatch::nth_match`, `RMatch::backref_number`,
  `RMatch::matched`, `RMatch::pre`, `RMatch::post`, and `RMatch::last`
- `RBignum::is_positive`/`is_negative`.
- `new`, `num`, and `den` for `RRational`, plus `rationalize` and
  `rationalize_with_prec` for `Float`.
- `RComplex::new`, `polar`, `real`, `imag`, `conjugate`, `abs` & `arg`.
- New `Numeric` trait implemented for `Integer`, `Float`, `RRational`,
  `RComplex`, etc. Exposes functions for applying operators to numeric types
  following Ruby's coercion protocol.
- `value::Id::new` added to replace `value::Id::from`.
- `TypedData::class_for` can be implemented to customise the class on a case by
  case basis when wrapping Rust data in a Ruby object.
- The `#[wrap]` and `#[derive(TypedData)]` macros now allow setting
  `#[magnus(class = "...")]` on enum variants to customise the class per
  variant when wrapping enums in a Ruby object.
- `Value::funcall_public` calls a public method, returning an error for a
  private or protected method.
- `error::Result<T>` is shorthand for `std::result::Result<T, Error>`.
- `embed::setup` to perform minimal initialisation of Ruby for environments
  where `embed::init` doesn't work.
- The `bytes-crate` feature can be enabled to allow automatic conversions
  between `bytes::Bytes` and Ruby strings.

### Changed
- When converting Ruby values to `RArray` (or `Vec<T>`, `[T; 1]`, or `(T,)`),
  an error will be returned if given a non-`Array` (or non-`to_ary`-able) value,
  rather than wrapping it in an array (see `RArray::to_ary` for the old
  behaviour).
- `r_typed_data::{DataType, DataTypeFunctions, DataTypeBuilder, TypedData}` all
  moved to `typed_data` module, `r_typed_data` module removed. This should only
  affect `DataTypeBuilder` as it was the only one not exported at the crate
  root.
- `gc::adjust_memory_usage`'s argument changed to `isize`, rather than `i32` or
  `i64` depending on pointer width.
- The `IntoValue` trait is now used instead of `Into<Value>` for converting to
  Ruby types.
- `IntoId`, `IntoRString`, and `IntoSymbol` are used instead of `Into<Id>`,
  `Into<RString>`, and `Into<Symbol>`.
- `use magnus::prelude::*` will now import traits anonymously.
- `EncodingCapable`, `Module`, `Class`, and `Object` traits can no longer be
  implemented by user code.
- The `wb_protected` flag is automatically set for data wrapped in a Ruby
  object when `mark` is not set.

### Deprecated
- `RString::append` (use `RString::buf_append`).
- `Error::runtime_error` (use `Error::new(exception::runtime_error(), msg)`).
- Implementations of `Into<Value>` (use `IntoValue`).

### Removed
- `DataTypeBuilder::free_immediatly` (use `free_immediately`).
- `From<&str> for RString` / `Into<RString> for &str`.
- `From<String> for RString` / `Into<RString> for String`.
- `From<&str> for Symbol` / `Into<Symbol> for &str`.
- `From<String> for Symbol` / `Into<Symbol> for String`.
- `From<&str> for StaticSymbol` / `Into<StaticSymbol> for &str`.
- `From<String> for StaticSymbol` / `Into<StaticSymbol> for String`.
- `From<&str> for Id` / `Into<Id> for &str`.
- `From<String> for Id` / `Into<Id> for String`.
- Internal `debug_assert_value!()` macro no longer public.

### Fixed
- Missing `ReprValue` implementation for `RStruct`.

## [0.4.4] - 2022-12-24
### Added
- `Class::undef_alloc_func`, a function to remove a class' allocator function.

### Fixed
- 'wrapped' structs from `#[wrap]` and `#[derive(TypedData)]` macros will not
  generate `warning: undefining the allocator of T_DATA class` under Ruby 3.2

## [0.4.3] - 2022-12-07
### Fixed
- `gc::mark_slice` was skipping the last element of the slice.

## [0.4.2] - 2022-11-30
### Fixed
- Removed errant `dbg!()`.

## [0.4.1] - 2022-11-29
### Fixed
- `scan_args::get_kwargs` error/segfault when leading optional args were not
  provided, due to trying to convert the type of the missing value.

## [0.4.0] - 2022-11-19
### Added
- `Value::funcall_with_block`.
- impl `TryConvert` for `Exception` and `ExceptionClass`.
- `Class` trait (implemented for `RClass` and `ExceptionClass`).
- `define_error` and `Module::define_error` helpers for defining an Exception
  Class.
- `RTypedData::wrap` and `RTypedData::get` inherent methods for wrapping Rust
  types in Ruby objects.
- Support for Ruby 3.2 preview.
- Support for mswin platform (msvc) on Windows with Ruby 3.2 (in addition to
  the mingw support previously available for all Ruby versions on Windows).

### Changed
- Switched to rb-sys for low level bindings.
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
- `DataTypeBuilder::free_immediatly` (use `free_immediately`).
- `free_immediatly` attribute in `wrap` macro (use `free_immediately`).
- `free_immediatly` in `magnus` attribute of `derive(TypedData)` macro
  (use `free_immediately`).

### Removed
- `String::encode_utf8`, use `r_string.conv_enc(RbEncoding::utf8())` instead.
- `Value::leak`, use `gc::register_mark_object` instead.
- `define_global_variable` (use `define_variable`).

### Fixed
- Memory leak of the message when returning an `Error` to raise an exception.
- `Flonum` support disabled for Ruby built with USE_FLONUM=0 (e.g. 32 bit
  systems).
- Correct spelling of `free_immediatly` (to `free_immediately`) in the
  `DataTypeBuilder` struct, and `wrap` and `derive(TypedData)` macros.

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
- `Exception::backtrace`, use `ex.funcall("backtrace", ())` instead.

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

[Unreleased]: https://github.com/matsadler/magnus/compare/0.6.0...HEAD
[0.6.0]: https://github.com/matsadler/magnus/compare/0.5.3...0.6.0
[0.5.3]: https://github.com/matsadler/magnus/compare/0.5.2...0.5.3
[0.5.2]: https://github.com/matsadler/magnus/compare/0.5.1...0.5.2
[0.5.1]: https://github.com/matsadler/magnus/compare/0.5.0...0.5.1
[0.5.0]: https://github.com/matsadler/magnus/compare/0.4.4...0.5.0
[0.4.4]: https://github.com/matsadler/magnus/compare/0.4.3...0.4.4
[0.4.3]: https://github.com/matsadler/magnus/compare/0.4.2...0.4.3
[0.4.2]: https://github.com/matsadler/magnus/compare/0.4.1...0.4.2
[0.4.1]: https://github.com/matsadler/magnus/compare/0.4.0...0.4.1
[0.4.0]: https://github.com/matsadler/magnus/compare/0.3.2...0.4.0
[0.3.2]: https://github.com/matsadler/magnus/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/matsadler/magnus/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/matsadler/magnus/compare/0.2.1...0.3.0
[0.2.1]: https://github.com/matsadler/magnus/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/matsadler/magnus/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/matsadler/magnus/tree/0.1.0

# Magnus

Ruby bindings for Rust. Write Ruby extension gems in Rust, or call Ruby code
from a Rust binary.

## Type Conversions

Magnus will automatically convert between Rust and Ruby types, including
converting Ruby exceptions to Rust `Result`s and visa versa.

These conversions follow the pattern set by Ruby's core and standard libraries,
where many conversions will delegate to a `#to_<type>` method if the object is
not of the requested type, but does implement the `#to_<type>` method.

Below are tables outlining many common conversions. See the Magnus api
documentation for the full list of types.

### Rust functions accepting values from Ruby

See `magnus::TryConvert` for more details.

| Rust function argument                            | accepted from Ruby                                    |
|---------------------------------------------------|-----------------------------------------|
| `i8`,`i16`,`i32`,`i64`,`isize`, `magnus::Integer` | `Integer`, `#to_int`                    |
| `u8`,`u16`,`u32`,`u64`,`usize`                    | `Integer`, `#to_int`                    |
| `f32`,`f64`, `magnus::Float`                      | `Float`, `Numeric`                      |
| `String`, `PathBuf`, `char`, `magnus::RString`    | `String`, `#to_str`                     |
| `magnus::Symbol`                                  | `Symbol`, `#to_sym`                     |
| `bool`                                            | any object                              |
| `Option<T>`                                       | `T` or `nil`                            |
| `(T, U)`, `(T, U, V)`, etc                        | `[T, U]`, `[T, U, V]`, etc, `#to_ary`   |
| `[T; N]`                                          | `[T]`, `#to_ary`                        |
| `magnus::RArray`                                  | `Array`, `#to_ary`                      |
| `magnus::RHash`                                   | `Hash`, `#to_hash`                      |
| `magnus::Value`                                   | any object                              |
| `Vec<T>`*                                         | `[T]`, `#to_ary`                        |
| `HashMap<K, V>`*                                  | `{K => V}`, `#to_hash`                  |
| `&T where T: TypedData`**                         | instance of `<T as TypedData>::class()` |

\* when converting to `Vec` and `HashMap` the types of `T`/`K`,`V` must be native Rust types.

\** see the `wrap` macro.

### Rust returning / passing values to Ruby

See the `magnus::Value` type, for all types implementing `Into<Value>`, plus
`magnus::method::ReturnValue` and `magnus::ArgList` for some additional details.

| returned from Rust / calling Ruby from Rust       | received in Ruby                        |
|---------------------------------------------------|-----------------------------------------|
| `i8`,`i16`,`i32`,`i64`,`isize`                    | `Integer`                               |
| `u8`,`u16`,`u32`,`u64`,`usize`                    | `Integer`                               |
| `f32`, `f64`                                      | `Float`                                 |
| `String`, `&str`, `char`, `&Path`, `PathBuf`      | `String`                                |
| `bool`                                            | `true`/`false`                          |
| `()`                                              | `nil`                                   |
| `Option<T>`                                       | `T` or `nil`                            |
| `Result<T, magnus::Error>` (return only)          | `T` or raises error                     |
| `(T, U)`, `(T, U, V)`, etc, `[T; N]`, `Vec<T>`    | `Array`                                 |
| `HashMap<K, V>`                                   | `Hash`                                  |
| `T where T: TypedData`**                          | instance of `<T as TypedData>::class()` |

\** see the `wrap` macro.

### Manual Conversions

There may be cases where you want to bypass the automatic type conversions, to
do this use the type `magnus::Value` and then manually convert or type check
from there.

For example, if you wanted to ensure your function is always passed a UTF-8
encoded String so you can take a reference without allocating you could do the
following:

```
fn example(val: magnus::Value) -> Result<(), magnus::Error> {
    // checks value is a String, does not call #to_str
    let r_string = RString::from_value(val).ok_or_else(|| magnus::Error::type_error("expected string"))?;
    // error on encodings that would otherwise need converting to utf-8
    if !r_string.is_utf8_compatible_encoding() {
        return Err(magnus::Error::encoding_error("string must be utf-8"));
    }
    // RString::as_str is unsafe as it's possible for Ruby to invalidate the
    // str as we hold a reference to it. The easiest way to ensure the &str
    // stays valid is to avoid any other calls to Ruby for the life of the
    // reference (the rest of the unsafe block).
    unsafe {
        let s = r_string.as_str()?;
        // ...
    }
    Ok(())
}
```

## Safety

When using Magnus, in Rust code, Ruby objects must be kept on the stack. If
objects are moved to the heap the Ruby GC can not reach them, and they may be
garbage collected. This could lead to memory safety issues.

It is not possible to enforce this rule in Rust's type system or via the borrow
checker, users of Magnus must maintain this rule manually.

While it would be possible to mark any functions that could expose this unsafty
as `unsafe`, that would mean that almost every interaction with Ruby would
be `unsafe`. This would leave no way to differentiate the *really* unsafe
functions that need much more care to use.

Other than this, Magnus strives to match Rust's usual safety guaranties for
users of the library. Magnus itself contains a large amount of code marked with
the `unsafe` keyword, it is impossible to interact with Ruby's C-api without
this, but users of Magnus should be able to do most things without needing to
use `unsafe`.

## Writing an extension gem (calling Rust from Ruby)

TODO

## Embedding Ruby in Rust

TODO

## Alternatives

* [rutie](https://github.com/danielpclark/rutie)
* [rosy](https://github.com/nvzqz/rosy)
* [ruby-sys](https://github.com/steveklabnik/ruby-sys)
* [ruru](https://github.com/d-unseductable/ruru)
* [plugger](https://github.com/dylanmckay/plugger)
* [helix](https://github.com/tildeio/helix)

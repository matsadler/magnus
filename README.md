# Magnus

Ruby bindings for Rust. Write Ruby extension gems in Rust, or call Ruby code
from a Rust binary.

[API Docs] | [GitHub] | [crates.io]

[API Docs]: https://docs.rs/magnus/latest/magnus/
[GitHub]: https://github.com/matsadler/magnus
[crates.io]: https://crates.io/crates/magnus

## Defining Methods

Using Magnus, regular Rust functions can be bound to Ruby as methods with
automatic type conversion. Callers passing the wrong arguments or incompatible
types will get the same kind of `ArgumentError` or `TypeError` they are used to
seeing from Ruby's built in methods.

Defining a function (with no Ruby `self` argument):
```rust
fn fib(n: usize) -> usize {
    match n {
        0 => 0,
        1 | 2 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}

magnus::define_global_function("fib", magnus::function!(fib, 1));
```

Defining a method (with a Ruby `self` argument):
```rust
fn is_blank(rb_self: String) -> bool {
    !rb_self.contains(|c: char| !c.is_whitespace())
}

let class = magnus::define_class("String", Default::default())?;
// 0 as self doesn't count against the number of arguments
class.define_method("blank?", magnus::method!(is_blank, 0))?;
```

## Calling Ruby Methods

Some Ruby methods have direct counterparts in Ruby's C API and therefore in
Magnus. Ruby's `Object#frozen?` method is available as
`magnus::Value::check_frozen`, or `Array#[]` becomes `magnus::RArray::aref`.

Other Ruby methods that are defined only in Ruby must be called with
`magnus::Value::funcall`. All of Magnus' Ruby wrapper types deref to `Value`,
so `funcall` can be used on all of them.

```rust
let s: String = value.funcall("test", ())?; // 0 arguments
let x: bool = value.funcall("example", ("foo",))?; // 1 argument
let i: i64 = value.funcall("other", (42, false))?; // 2 arguments, etc
```

`funcall` will convert return types, returning `Err(magnus::Error)` if the type
conversion fails or the method call raised an error. To skip type conversion
make sure the return type is `magnus::Value`.

## Wrapping Rust Types in Ruby Objects

Rust structs and enums can be wrapped in Ruby objects so they can be returned
to Ruby.

Types can opt-in to this with the `magnus::wrap` macro (or by implementing
`magnus::TypedData`). Whenever a compatible type is returned to Ruby it will be
wrapped in the specified class, and whenever it is passed back to Rust it will
be unwrapped to a reference.

```rust
use magnus::{define_class, function, method, prelude::*, Error};

#[magnus::wrap(class = "Point")]
struct Point {
    x: isize,
    y: isize,
}

impl Point {
    fn new(x: isize, y: isize) -> Self {
        Self { x, y }
    }

    fn x(&self) -> isize {
        self.x
    }

    fn y(&self) -> isize {
        self.y
    }

    fn distance(&self, other: &Point) -> f64 {
        (((other.x - self.x).pow(2) + (other.y - self.y).pow(2)) as f64).sqrt()
    }
}

#[magnus::init]
fn init() -> Result<(), Error> {
    let class = define_class("Point", Default::default())?;
    class.define_singleton_method("new", function!(Point::new, 2))?;
    class.define_method("x", method!(Point::x, 0))?;
    class.define_method("y", method!(Point::y, 0))?;
    class.define_method("distance", method!(Point::distance, 1))?;
    Ok(())
}
```

The newtype pattern and `RefCell` can be used if mutability is required:

```rust
struct Point {
    x: isize,
    y: isize,
}

#[magnus::wrap(class = "Point")]
struct MutPoint(std::cell::RefCell<Point>);

impl MutPoint {
    fn set_x(&self, i: isize) {
        self.0.borrow_mut().x = i;
    }
}
```

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
| `magnus::Range`                                   | `Range`                                 |
| `magnus::Encoding`, `magnus::RbEncoding`          | `Encoding`, encoding name as a string   |
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
| `Range`, `RangeFrom`, `RangeTo`, `RangeInclusive` | `Range`                                 |
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

```rust
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

Ruby extensions must be built as dynamic system libraries, this can be done by
setting the `crate-type` attribute in your `Cargo.toml`.

**`Cargo.toml`**
```toml
[lib]
crate-type = ["cdylib"]

[dependencies]
magnus = "0.2"
```

When Ruby loads your extension it calls an 'init' function defined in your
extension. In this function you will need to define your Ruby classes and bind
Rust functions to Ruby methods. Use the `#[magnus::init]` attribute to mark
your init function so it can be correctly exposed to Ruby.

**`src/lib.rs`**
```rust
use magnus::{define_global_function, function};

fn distance(a: (f64, f64), b: (f64, f64)) -> f64 {
    ((b.0 - a.0).powi(2) + (b.1 - a.1).powi(2)).sqrt()
}

#[magnus::init]
fn init() {
    define_global_function("distance", function!(distance, 2));
}
```

If you wish to package your extension as a Gem, Rubygems currently does not
support Rust extensions directly, but a Rakefile can be used to compile your
Rust extension when the gem is installed.

**`my_example_gem.gemspec`**
```ruby
spec.extensions = ["ext/my_example_gem/Rakefile"]

# actually a build time dependency, but that's not an option.
spec.add_runtime_dependency "rake", "> 1"
```

See the [`rust_blank`] example for an example Rakefile that can be copied into
your project without changes. This Rakefile will place the extension at
`lib/my_example_gem/my_example_gem.so` (or `.bundle` on macOS), which you'd
load from Ruby like so:

**`lib/my_example_gem.rb`**
```ruby
require_relative "my_example_gem/my_example_gem"
```

[`rust_blank`]: https://github.com/matsadler/magnus/tree/main/examples/rust_blank/ext/rust_blank

### Compiling Extensions

If you are compiling your extension yourself outside of Rubygems you will need
to pass a number of compiler flags as specified by `ruby -e'p
RbConfig::CONFIG["DLDFLAGS"]'`. These may need translating from C compiler args
to rustc args. At a minimum the following should work most of the time:

```shell
cargo rustc --release -- -C link-arg=-Wl,-undefined,dynamic_lookup
```

The compiled library will need to be moved from Cargo's target directory into
Ruby's load path. On Linux and macOS the library will have the prefix `lib`
added to the extension name, typically you'd want to rename the file to remove
this prefix so that you do not need to include it in your Ruby `require`s.
Additionally on macOS the file extension will need to be changed from `.dylib`
to `.bundle`.

## Embedding Ruby in Rust

To call Ruby from a Rust program, enable the `embed` feature:

**`Cargo.toml`**
```toml
[dependencies]
magnus = { version = "0.2", features = ["embed"] }
```

This enables linking to Ruby and gives access to the `embed` module.
`magnus::embed::init` must be called before calling Ruby and the value it
returns must not be dropped until you are done with Ruby. `init` can not be
called more than once.

**`src/main.rs`**
```rust
use magnus::{embed, eval};

fn main() {
    let _cleanup = unsafe { embed::init() };

    let val: f64 = eval!("a + rand", a = 1).unwrap();

    println!("{}", val);
}
```

## Compatibility

Magnus contains pre-built bindings for Ruby 2.6 through 3.1 on Linux x86_64,
macOS x86_64, macOS aarch64, and Windows x86_64.
For other Ruby version/platform combinations bindings will be generated at
compile time, this may require libclang to be installed.

The Minimum supported Rust version is currently Rust 1.51.

Support for statically linking Ruby is provided, but not tested.

Support for 32 bit systems is almost certainly broken, patches are welcome.

### rb-sys

Magnus can use [rb-sys] to provide the low-level bindings to Ruby through the
`rb-sys-interop` feature. This also enables the
[`rb_sys`](https://docs.rs/magnus/latest/magnus/rb_sys/index.html) module for
interoperability with rb-sys.

[rb-sys]: https://github.com/oxidize-rb/rb-sys

This can be enabled with:

**`Cargo.toml`**
```toml
[dependencies]
magnus = { version = "0.3", features = ["rb-sys-interop"] }
```

This feature should be considered a preview and will be reworked/expanded in
future versions.

## Alternatives

* [rutie](https://github.com/danielpclark/rutie)
* [rb-sys]
* [rosy](https://github.com/nvzqz/rosy)
* [ruby-sys](https://github.com/steveklabnik/ruby-sys)
* [ruru](https://github.com/d-unseductable/ruru)
* [plugger](https://github.com/dylanmckay/plugger)
* [helix](https://github.com/tildeio/helix)

## Naming

Magnus is named after Magnus the Red a character from the Warhammer 40,000
universe. A sorcerer who believed he could tame the psychic energy of the Warp.
Ultimately, his hubris lead to his fall to Chaos, but lets hope using this
library turns out better for you.

## License

This project is licensed under the MIT license, see LICENSE.

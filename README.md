# Magnus

High level Ruby bindings for Rust. Write Ruby extension gems in Rust, or call
Ruby code from a Rust binary.

[API Docs] | [GitHub] | [crates.io]

[API Docs]: https://docs.rs/magnus/latest/magnus/
[GitHub]: https://github.com/matsadler/magnus
[crates.io]: https://crates.io/crates/magnus

[Getting Started] | [Type Conversions] | [Safety] | [Compatibility]

[Getting Started]: #getting-started
[Type Conversions]: #type-conversions
[Safety]: #safety
[Compatibility]: #compatibility

## Examples

### Defining Methods

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

#[magnus::init]
fn init(ruby: &magnus::Ruby) -> Result<(), Error> {
    ruby.define_global_function("fib", magnus::function!(fib, 1));
    Ok(())
}
```

Defining a method (with a Ruby `self` argument):

```rust
fn is_blank(rb_self: String) -> bool {
    !rb_self.contains(|c: char| !c.is_whitespace())
}

#[magnus::init]
fn init(ruby: &magnus::Ruby) -> Result<(), Error> {
    // returns the existing class if already defined
    let class = ruby.define_class("String", ruby.class_object())?;
    // 0 as self doesn't count against the number of arguments
    class.define_method("blank?", magnus::method!(is_blank, 0))?;
    Ok(())
}
```

### Calling Ruby Methods

Some Ruby methods have direct counterparts in Ruby's C API and therefore in
Magnus. Ruby's `Object#frozen?` method is available as
`magnus::ReprValue::check_frozen`, or `Array#[]` becomes `magnus::RArray::aref`.

Other Ruby methods that are defined only in Ruby must be called with
`magnus::ReprValue::funcall`. All of Magnus' Ruby wrapper types implement the
`ReprValue` trait, so `funcall` can be used on all of them.

```rust
let s: String = value.funcall("test", ())?; // 0 arguments
let x: bool = value.funcall("example", ("foo",))?; // 1 argument
let i: i64 = value.funcall("other", (42, false))?; // 2 arguments, etc
```

`funcall` will convert return types, returning `Err(magnus::Error)` if the type
conversion fails or the method call raised an error. To skip type conversion
make sure the return type is `magnus::Value`.

### Wrapping Rust Types in Ruby Objects

Magnus allows you to wrap Rust structs and enums as Ruby objects, enabling seamless interaction between Rust and Ruby. This functionality is ideal for exposing Rust logic to Ruby modules.

Use one of the following approaches to expose a Rust type to Ruby:

* A convenience macro [`#[magnus::wrap]`][magnus-wrap].
* More customised approach by implementing the [`magnus::TypedData`] trait.

[magnus-wrap]: https://docs.rs/magnus/latest/magnus/attr.wrap.html
[`magnus::TypedData`]: https://docs.rs/magnus/latest/magnus/derive.TypedData.html

Then this Rust type can be:

* Returned to Ruby as a wrapped object.
* Passed back to Rust and automatically unwrapped to a native Rust reference.

#### Basic Usage

Here’s how you can wrap a simple Rust struct and expose its methods to Ruby:

```rust
use magnus::{function, method, prelude::*, Error, Ruby};

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
fn init(ruby: &Ruby) -> Result<(), Error> {
    let class = ruby.define_class("Point", ruby.class_object())?;
    class.define_singleton_method("new", function!(Point::new, 2))?;
    class.define_method("x", method!(Point::x, 0))?;
    class.define_method("y", method!(Point::y, 0))?;
    class.define_method("distance", method!(Point::distance, 1))?;
    Ok(())
}
```

#### Handling Mutability

Because Ruby's GC manages the memory where your Rust type is stored, Magnus can't bind functions with mutable references. To allow mutable fields in wrapped Rust structs, you can use the newtype pattern with `RefCell`:

```rust
use std::cell::RefCell;

struct Point {
    x: isize,
    y: isize,
}

#[magnus::wrap(class = "Point")]
struct MutPoint(RefCell<Point>);

impl MutPoint {
    fn set_x(&self, i: isize) {
        self.0.borrow_mut().x = i;
    }
}
```

See [`examples/mut_point.rs`] for the complete example.

[`examples/mut_point.rs`]: https://github.com/matsadler/magnus/blob/main/examples/mut_point.rs

#### Supporting Subclassing

To enable Ruby subclassing for wrapped Rust types, the type must:

* Implement the `Default` trait.
* Define an allocator.
* Define an initialiser.

``` rust
#[derive(Default)]
struct Point {
    x: isize,
    y: isize,
}

#[derive(Default)]
#[wrap(class = "Point")]
struct MutPoint(RefCell<Point>);

impl MutPoint {
    fn initialize(&self, x: isize, y: isize) {
        let mut this = self.0.borrow_mut();
        this.x = x;
        this.y = y;
    }
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    let class = ruby.define_class("Point", ruby.class_object()).unwrap();
    class.define_alloc_func::<MutPoint>();
    class.define_method("initialize", method!(MutPoint::initialize, 2))?;
    Ok(())
}
```

#### Error Handling

Use `magnus::Error` to propagate errors to Ruby from Rust:

```rust
#[magnus::wrap(class = "Point")]
struct MutPoint(RefCell<Point>);

impl MutPoint {
    fn add_x(ruby: &Ruby, rb_self: &Self, val: isize) -> Result<isize, Error> {
        if let Some(sum) = rb_self.0.borrow().x.checked_add(val) {
            rb_self.0.borrow_mut().x = sum;
            Ok(sum)
        } else {
            return Err(Error::new(ruby.exception_range_error(), "result out of range"));
        }
    }
}
```

## Getting Started

### Writing an extension gem (calling Rust from Ruby)

Ruby extensions must be built as dynamic system libraries, this can be done by
setting the `crate-type` attribute in your `Cargo.toml`.

**`Cargo.toml`**

```toml
[lib]
crate-type = ["cdylib"]

[dependencies]
magnus = "0.8"
```

When Ruby loads your extension it calls an 'init' function defined in your
extension. In this function you will need to define your Ruby classes and bind
Rust functions to Ruby methods. Use the `#[magnus::init]` attribute to mark
your init function so it can be correctly exposed to Ruby.

**`src/lib.rs`**

```rust
use magnus::{function, Error, Ruby};

fn distance(a: (f64, f64), b: (f64, f64)) -> f64 {
    ((b.0 - a.0).powi(2) + (b.1 - a.1).powi(2)).sqrt()
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    ruby.define_global_function("distance", function!(distance, 2));
}
```

If you wish to package your extension as a Gem, we recommend using the
[`rb_sys` gem] to build along with `rake-compiler`. These tools will
automatically build your Rust extension as a dynamic library, and then package
it as a gem.

*Note*: The newest version of rubygems does have beta support for compiling
Rust, so in the future the `rb_sys` gem won't be necessary.

**`my_example_gem.gemspec`**
```ruby
spec.extensions = ["ext/my_example_gem/extconf.rb"]

# needed until rubygems supports Rust support is out of beta
spec.add_dependency "rb_sys", "~> 0.9.39"

# only needed when developing or packaging your gem
spec.add_development_dependency "rake-compiler", "~> 1.2.0"
```

Then, we add an `extconf.rb` file to the `ext` directory. Ruby will execute
this file during the compilation process, and it will generate a `Makefile` in
the `ext` directory. See the [`rb_sys` gem] for more information.

**`ext/my_example_gem/extconf.rb`**

```ruby
require "mkmf"
require "rb_sys/mkmf"

create_rust_makefile("my_example_gem/my_example_gem")
```

See the [`rust_blank`] example for examples of `extconf.rb` and `Rakefile`.
Running `rake compile` will place the extension at
`lib/my_example_gem/my_example_gem.so` (or `.bundle` on macOS), which you'd
load from Ruby like so:

**`lib/my_example_gem.rb`**

```ruby
require_relative "my_example_gem/my_example_gem"
```

For a more detailed example (including cross-compilation and more), see the
[`rb-sys` example project]. Although the code in `lib.rs` does not feature
magnus, but it will compile and run properly.

[`rb_sys` gem]: https://github.com/oxidize-rb/rb-sys/tree/main/gem
[`rake-compiler`]: https://github.com/rake-compiler/rake-compiler
[`rust_blank`]: https://github.com/matsadler/magnus/tree/main/examples/rust_blank/ext/rust_blank
[`rb-sys` example project]: https://github.com/oxidize-rb/rb-sys/tree/main/examples/rust_reverse

### Embedding Ruby in Rust

To call Ruby from a Rust program, enable the `embed` feature:

**`Cargo.toml`**

```toml
[dependencies]
magnus = { version = "0.8", features = ["embed"] }
```

This enables linking to Ruby and gives access to the `embed` module.
`magnus::embed::init` must be called before calling Ruby and the value it
returns must not be dropped until you are done with Ruby. `init` can not be
called more than once.

**`src/main.rs`**

```rust
use magnus::eval;

fn main() {
    magnus::Ruby::init(|ruby| {
        let val: f64 = eval!(ruby, "a + rand", a = 1)?;

        println!("{}", val);

        Ok(())
    }).unwrap();
}
```

## Type Conversions

Magnus will automatically convert between Rust and Ruby types, including
converting Ruby exceptions to Rust `Result`s and vice versa.

These conversions follow the pattern set by Ruby's core and standard libraries,
where many conversions will delegate to a `#to_<type>` method if the object is
not of the requested type, but does implement the `#to_<type>` method.

Below are tables outlining many common conversions. See the Magnus api
documentation for the full list of types.

### Rust functions accepting values from Ruby

See `magnus::TryConvert` for more details.

| Rust function argument                                               | accepted from Ruby                      |
| -------------------------------------------------------------------- | --------------------------------------- |
| `i8`,`i16`,`i32`,`i64`,`isize`, `magnus::Integer`                    | `Integer`, `#to_int`                    |
| `u8`,`u16`,`u32`,`u64`,`usize`                                       | `Integer`, `#to_int`                    |
| `f32`,`f64`, `magnus::Float`                                         | `Float`, `Numeric`                      |
| `String`, `PathBuf`, `char`, `magnus::RString`, `bytes::Bytes`‡      | `String`, `#to_str`                     |
| `magnus::Symbol`                                                     | `Symbol`, `#to_sym`                     |
| `bool`                                                               | any object                              |
| `magnus::Range`                                                      | `Range`                                 |
| `magnus::Encoding`, `magnus::RbEncoding`                             | `Encoding`, encoding name as a string   |
| `Option<T>`                                                          | `T` or `nil`                            |
| `(T, U)`, `(T, U, V)`, etc                                           | `[T, U]`, `[T, U, V]`, etc, `#to_ary`   |
| `[T; N]`                                                             | `[T]`, `#to_ary`                        |
| `magnus::RArray`                                                     | `Array`, `#to_ary`                      |
| `magnus::RHash`                                                      | `Hash`, `#to_hash`                      |
| `std::time::SystemTime`, `magnus::Time`, `chrono::DateTime<T>`§      | `Time`                                  |
| `magnus::Value`                                                      | any object                              |
| `Vec<T>`\*                                                           | `[T]`, `#to_ary`                        |
| `HashMap<K, V>`\*                                                    | `{K => V}`, `#to_hash`                  |
| `&T`, `typed_data::Obj<T>` where `T: TypedData`†                     | instance of `<T as TypedData>::class()` |

\* when converting to `Vec` and `HashMap` the types of `T`/`K`,`V` must be native Rust types.

† see the `wrap` macro.

‡ when the `bytes` feature is enabled

§ when the `chrono` feature is enabled; `T` can be `Utc` or `FixedOffset`.

### Rust returning / passing values to Ruby

See `magnus::IntoValue` for more details, plus `magnus::method::ReturnValue`
and `magnus::ArgList` for some additional details.

| returned from Rust / calling Ruby from Rust        | received in Ruby                        |
| -------------------------------------------------- | --------------------------------------- |
| `i8`,`i16`,`i32`,`i64`,`isize`                     | `Integer`                               |
| `u8`,`u16`,`u32`,`u64`,`usize`                     | `Integer`                               |
| `f32`, `f64`                                       | `Float`                                 |
| `String`, `&str`, `char`, `&Path`, `PathBuf`       | `String`                                |
| `bool`                                             | `true`/`false`                          |
| `()`                                               | `nil`                                   |
| `Range`, `RangeFrom`, `RangeTo`, `RangeInclusive`  | `Range`                                 |
| `Option<T>`                                        | `T` or `nil`                            |
| `Result<T, magnus::Error>` (return only)           | `T` or raises error                     |
| `(T, U)`, `(T, U, V)`, etc, `[T; N]`, `Vec<T>`     | `Array`                                 |
| `HashMap<K, V>`                                    | `Hash`                                  |
| `std::time::SystemTime`                            | `Time`                                  |
| `T`, `typed_data::Obj<T>` where `T: TypedData`\*  | instance of `<T as TypedData>::class()` |

\* see the `wrap` macro.

### Conversions via Serde

Rust types can also be converted to Ruby, and vice versa, using [Serde] with
the [`serde_magnus`] crate.

[Serde]: https://github.com/serde-rs/serde
[`serde_magnus`]: https://github.com/OneSignal/serde-magnus

### Manual Conversions

There may be cases where you want to bypass the automatic type conversions, to
do this use the type `magnus::Value` and then manually convert or type check
from there.

For example, if you wanted to ensure your function is always passed a UTF-8
encoded String so you can take a reference without allocating you could do the
following:

```rust
fn example(ruby: &Ruby, val: magnus::Value) -> Result<(), magnus::Error> {
    // checks value is a String, does not call #to_str
    let r_string = RString::from_value(val)
        .ok_or_else(|| magnus::Error::new(ruby.exception_type_error(), "expected string"))?;
    // error on encodings that would otherwise need converting to utf-8
    if !r_string.is_utf8_compatible_encoding() {
        return Err(magnus::Error::new(
            ruby.exception_encoding_error(),
            "string must be utf-8",
        ));
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

An example of something that breaks this rule would be storing a Ruby object in
a Rust heap allocated data structure, such as `Vec`, `HashMap`, or `Box`. This
must be avoided at all costs.

While it would be possible to mark any functions that could expose this unsafty
as `unsafe`, that would mean that almost every interaction with Ruby would
be `unsafe`. This would leave no way to differentiate the *really* unsafe
functions that need much more care to use.

Other than this, Magnus strives to match Rust's usual safety guaranties for
users of the library. Magnus itself contains a large amount of code marked with
the `unsafe` keyword, it is impossible to interact with Ruby's C-api without
this, but users of Magnus should be able to do most things without needing to
use `unsafe`.

## Compatibility

Ruby versions 3.0, 3.1, 3.2, 3.3 and 3.4 are fully supported.

Magnus currently works with, and is still tested against, Ruby 2.7, but as this
version of the language is no longer supported by the Ruby developers it is not
recommended and future support in Magnus is not guaranteed.

Ruby bindings will be generated at compile time, this may require libclang to
be installed.

The minimum supported Rust version is currently Rust 1.71.

Support for statically linking Ruby is provided via the lower-level [rb-sys]
crate, and can be enabled by adding the following to your `Cargo.toml`:

```toml
# * should select the same version used by Magnus
rb-sys = { version = "*", default-features = false, features = ["ruby-static"] }
```

Cross-compilation is supported by rb-sys [for the platforms listed here][plat].

Magnus is not tested on 32 bit systems. Efforts are made to ensure it compiles.
Patches are welcome.

[plat]: https://github.com/oxidize-rb/rb-sys#supported-platforms

## Crates that work with Magnus

### rb-sys

Magnus uses [rb-sys] to provide the low-level bindings to Ruby. The
`rb-sys` feature enables the [`rb_sys`][rb_sys_module] module for
advanced interoperability with rb-sys, allows you to access low-level Ruby APIs
which Magnus does not expose.

[rb-sys]: https://github.com/oxidize-rb/rb-sys/tree/main/crates/rb-sys
[rb_sys_module]: https://docs.rs/magnus/latest/magnus/rb_sys/index.html

### `serde_magnus`

[`serde_magnus`] integrates [Serde] and Magnus for seamless serialisation and
deserialisation of Rust to Ruby data structures and vice versa.

## Users

* [`halton`](https://github.com/matsadler/halton-rb) a Ruby gem providing a
  highly optimised method for generating Halton sequences.
* [`optify`](https://github.com/juharris/optify) a Ruby gem to
  simplify using configuration files to manage options for experiments.
  It has a GitHub action to publish the gem for different architectures to RubyGems
  with a RBI file for type hints.

Please open a [pull request](https://github.com/matsadler/magnus/pulls) if
you'd like your project listed here.

## Troubleshooting

### Issues with static linking

If you encounter an error such as `symbol not found in flat namespace
'_rb_ext_ractor_safe'` when embedding static Ruby, you will need to instruct
Cargo not to strip code that it thinks is dead.

In you the same directory as your `Cargo.toml` file, create a
`.cargo/config.toml` file with the following contents:

```toml
[build]
# Without this flag, when linking static libruby, the linker removes symbols
# (such as `_rb_ext_ractor_safe`) which it thinks are dead code... but they are
# not, and they need to be included for the `embed` feature to work with static
# Ruby.
rustflags = ["-C", "link-dead-code=on"]
```

## Naming

Magnus is named after *Magnus the Red* a character from the Warhammer 40,000
universe. A sorcerer who believed he could tame the psychic energy of the Warp.
Ultimately, his hubris lead to his fall to Chaos, but let's hope using this
library turns out better for you.

## License

This project is licensed under the MIT license, see [LICENSE].

[LICENSE]: https://github.com/matsadler/magnus/blob/main/LICENSE

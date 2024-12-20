use std::cell::RefCell;

use magnus::{function, method, prelude::*, wrap, Error, Ruby};

struct Point {
    x: isize,
    y: isize,
}

// The `wrap` macro wraps a Rust type in a Ruby object, enabling seamless
// integration.
//
// Magnus uses two Ruby API functions to manage the struct:
// * `rb_data_typed_object_wrap`
// * `rb_check_typeddata`
//
// # Mutability
//
// Ruby's garbage collector (GC) manages memory for wrapped objects. This
// prevents using `&mut` references because Rust requires them to be unique,
// while Ruby GC may move objects unpredictably. To address this, you can use
// [`RefCell`](https://doc.rust-lang.org/std/cell/struct.RefCell.html) to
// enable interior mutability.
//
// # Error Handling
//
// Use [`magnus::Error`](https://docs.rs/magnus/latest/magnus/struct.Error.html)
// to propagate errors to Ruby.
// For example, you can raise a Ruby exception from Rust using Ruby's
// predefined exception classes.
//
// The syntax for methods like `add_x` differs slightly from typical Rust
// struct methods because it uses the
// [`method!` macro](https://docs.rs/magnus/latest/magnus/macro.method.html):
// * The first parameter, `ruby`, gives access to Ruby's runtime.
// * The second parameter, `rb_self`, is the Ruby object being called.
//
// See [`DataTypeFunctions`](https://docs.rs/magnus/latest/magnus/derive.DataTypeFunctions.html)
// and [`TypedData`](https://docs.rs/magnus/latest/magnus/derive.TypedData.html)
#[wrap(class = "Point")]
struct MutPoint(RefCell<Point>);

impl MutPoint {
    fn new(x: isize, y: isize) -> Self {
        Self(RefCell::new(Point { x, y }))
    }

    fn x(&self) -> isize {
        self.0.borrow().x
    }

    fn set_x(&self, val: isize) {
        self.0.borrow_mut().x = val;
    }

    fn add_x(ruby: &Ruby, rb_self: &Self, val: isize) -> Result<isize, Error> {
        if let Some(sum) = rb_self.0.borrow().x.checked_add(val) {
            rb_self.0.borrow_mut().x = sum;
            Ok(sum)
        } else {
            return Err(Error::new(
                ruby.exception_range_error(),
                "result out of range",
            ));
        }
    }

    fn y(&self) -> isize {
        self.0.borrow().y
    }

    fn set_y(&self, val: isize) {
        self.0.borrow_mut().y = val;
    }

    fn add_y(ruby: &Ruby, rb_self: &Self, val: isize) -> Result<isize, Error> {
        if let Some(sum) = rb_self.0.borrow().y.checked_add(val) {
            rb_self.0.borrow_mut().y = sum;
            Ok(sum)
        } else {
            return Err(Error::new(
                ruby.exception_range_error(),
                "result out of range",
            ));
        }
    }

    fn distance(&self, other: &MutPoint) -> f64 {
        (((other.x() - self.x()).pow(2) + (other.y() - self.y()).pow(2)) as f64).sqrt()
    }
}

fn main() -> Result<(), String> {
    magnus::Ruby::init(|ruby| {
        let class = ruby.define_class("Point", ruby.class_object())?;
        class.define_singleton_method("new", function!(MutPoint::new, 2))?;
        class.define_method("x", method!(MutPoint::x, 0))?;
        class.define_method("x=", method!(MutPoint::set_x, 1))?;
        class.define_method("add_x", method!(MutPoint::add_x, 1))?;
        class.define_method("y", method!(MutPoint::y, 0))?;
        class.define_method("y=", method!(MutPoint::set_y, 1))?;
        class.define_method("add_y", method!(MutPoint::add_y, 1))?;
        class.define_method("distance", method!(MutPoint::distance, 1))?;

        let d: f64 = ruby.eval(
            "a = Point.new(0, 0)
             b = Point.new(0, 0)
             b.x = 5
             b.y = 10
             a.distance(b)",
        )?;

        println!("{}", d);
        Ok(())
    })
}

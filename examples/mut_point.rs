use std::cell::RefCell;

use magnus::{define_class, embed, eval, function, method, prelude::*, wrap, Error};

struct Point {
    x: isize,
    y: isize,
}

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

    fn y(&self) -> isize {
        self.0.borrow().y
    }

    fn set_y(&self, val: isize) {
        self.0.borrow_mut().y = val;
    }

    fn distance(&self, other: &MutPoint) -> f64 {
        (((other.x() - self.x()).pow(2) + (other.y() - self.y()).pow(2)) as f64).sqrt()
    }
}

fn main() -> Result<(), Error> {
    let _cleanup = unsafe { embed::init() };

    let class = define_class("Point", Default::default())?;
    class.define_singleton_method("new", function!(MutPoint::new, 2))?;
    class.define_method("x", method!(MutPoint::x, 0))?;
    class.define_method("x=", method!(MutPoint::set_x, 1))?;
    class.define_method("y", method!(MutPoint::y, 0))?;
    class.define_method("y=", method!(MutPoint::set_y, 1))?;
    class.define_method("distance", method!(MutPoint::distance, 1))?;

    let d: f64 = eval(
        "a = Point.new(0, 0)
         b = Point.new(0, 0)
         b.x = 5
         b.y = 10
         a.distance(b)",
    )?;

    println!("{}", d);
    Ok(())
}

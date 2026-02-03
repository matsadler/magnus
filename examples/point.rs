use magnus::{function, method, prelude::*, wrap};

#[wrap(class = "Point")]
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

fn main() -> Result<(), magnus::Error> {
    magnus::Ruby::init(|ruby| {
        let class = ruby.define_class("Point", ruby.class_object())?;
        class.define_singleton_method("new", function!(Point::new, 2))?;
        class.define_method("x", method!(Point::x, 0))?;
        class.define_method("y", method!(Point::y, 0))?;
        class.define_method("distance", method!(Point::distance, 1))?;

        let d: f64 = ruby.eval(
            "a = Point.new(0, 0)
             b = Point.new(5, 10)
             a.distance(b)",
        )?;

        println!("{}", d);
        Ok(())
    })
}

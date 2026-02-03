use magnus::{function, method, prelude::*};

/// Building on top of `wrap`, we can rely on Rust's enum to dispatch based on enum variants.
/// Magnus will transform the types between Ruby and Rust.
#[magnus::wrap(class = "Shape")]
enum Shape {
    #[magnus(class = "Circle")]
    Circle { radius: f64 },
    #[magnus(class = "Rectangle")]
    Rectangle { x: f64, y: f64 },
}

impl Shape {
    fn new_circle(radius: f64) -> Self {
        Self::Circle { radius }
    }

    fn new_rectangle(x: f64, y: f64) -> Self {
        Self::Rectangle { x, y }
    }

    fn area(&self) -> f64 {
        match self {
            Shape::Circle { radius } => std::f64::consts::PI * radius * radius,
            Shape::Rectangle { x, y } => x * y,
        }
    }
}

fn print_area(s: &Shape) {
    println!("{}", s.area());
}

fn main() -> Result<(), magnus::Error> {
    // Normal Rust code
    let a = Shape::Circle { radius: 10.0 };
    let b = Shape::Rectangle { x: 10.0, y: 2.0 };
    print_area(&a);
    print_area(&b);

    // magnus binding running in Ruby
    magnus::Ruby::init(|ruby| {
        let shape_class = ruby.define_class("Shape", ruby.class_object())?;
        shape_class.undef_default_alloc_func();

        // inherit from Shape
        let circle_class = ruby.define_class("Circle", shape_class)?;
        circle_class.define_singleton_method("new", function!(Shape::new_circle, 1))?;
        circle_class.define_method("area", method!(Shape::area, 0))?;

        let rectangle_class = ruby.define_class("Rectangle", shape_class)?;
        rectangle_class.define_singleton_method("new", function!(Shape::new_rectangle, 2))?;
        rectangle_class.define_method("area", method!(Shape::area, 0))?;

        let d: f64 = ruby.eval(
            "a = Circle.new(10.0)
             b = Rectangle.new(10.0, 2.0)
             difference = a.area - b.area
             puts \"The difference of the area between the circle and the rectangle is #{difference}.\"
             difference",
        )?;

        println!("{}", d);
        Ok(())
    })
}

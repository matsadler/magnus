use magnus::{block::yield_value, define_global_function, method, Error, Value};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

fn flipflop(_rb_self: Value, mut val: bool) -> Result<(), Error> {
    val = yield_value(val)?;
    loop {
        val = yield_value(!val)?;
    }
}

#[test]
fn it_yields() {
    let _cleanup = unsafe { magnus::embed::init() };

    define_global_function("flipflop", method!(flipflop, 1));

    rb_assert!(
        "
    i = 0
    values = []
    flipflop(true) do |val|
      values << val
      i += 1 if val
      break if i > 5
      val
    end
    i == 6 && p(values) == [true, false, true, false, true, false, true, false, true, false, true]
    "
    );
}

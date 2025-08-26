use magnus::{Error, Ruby, Value, eval, method, rb_assert};

fn flipflop(ruby: &Ruby, _rb_self: Value, mut val: bool) -> Result<(), Error> {
    val = ruby.yield_value(val)?;
    loop {
        val = ruby.yield_value(!val)?;
    }
}

#[test]
fn it_yields() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("flipflop", method!(flipflop, 1));

    let values = ruby.ary_new();
    let i: Value = eval!(
        ruby,
        "
        i = 0
        flipflop(true) do |val|
          values << val
          i += 1 if val
          break if i > 5
          val
        end
        i
        ",
        values
    )
    .unwrap();

    rb_assert!(
        ruby,
        "i == 6 && values == [true, false, true, false, true, false, true, false, true, false, true]",
        i,
        values
    );
}

use magnus::{define_global_variable, eval, Value};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_makes_an_enumerator() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val: Value = eval(
        "
    class Test
      def each
         yield 1
         yield 2
         yield 3
      end
    end
    Test.new
    ",
    )
    .unwrap();

    let enumerator = val.enumeratorize("each", ());

    let _ = define_global_variable("$val", enumerator);

    rb_assert!("$val.next == 1");
    rb_assert!("$val.next == 2");
    rb_assert!("$val.next == 3");
}

use magnus::{define_global_variable, eval_static};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval_static($eval).ok().unwrap().to_bool())
    };
}

#[test]
fn it_makes_an_enumerator() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = eval_static(
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
    .ok()
    .unwrap();

    let enumerator = val.enumeratorize("each", ());

    let _ = define_global_variable("$val", enumerator);

    rb_assert!("$val.next == 1");
    rb_assert!("$val.next == 2");
    rb_assert!("$val.next == 3");
}

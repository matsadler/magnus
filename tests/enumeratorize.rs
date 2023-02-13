use magnus::{prelude::*, Value};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[test]
fn it_makes_an_enumerator() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val: Value = magnus::eval!(
        "
    class Test
      def each
         yield 1
         yield 2
         yield 3
      end
    end
    Test.new
    "
    )
    .unwrap();

    let enumerator = val.enumeratorize("each", ());

    rb_assert!("enumerator.next == 1", enumerator);
    rb_assert!("enumerator.next == 2", enumerator);
    rb_assert!("enumerator.next == 3", enumerator);
}

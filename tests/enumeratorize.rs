use magnus::{Value, prelude::*, rb_assert};

#[test]
fn it_makes_an_enumerator() {
    let ruby = unsafe { magnus::embed::init() };

    let val: Value = magnus::eval!(
        ruby,
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

    rb_assert!(ruby, "enumerator.next == 1", enumerator);
    rb_assert!(ruby, "enumerator.next == 2", enumerator);
    rb_assert!(ruby, "enumerator.next == 3", enumerator);
}

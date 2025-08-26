use magnus::{Ruby, Value, block::Yield, eval, method, prelude::*, rb_assert};

fn count_to_3(ruby: &Ruby, rb_self: Value) -> Yield<impl Iterator<Item = u8> + use<>> {
    if ruby.block_given() {
        Yield::Iter(1..=3)
    } else {
        Yield::Enumerator(rb_self.enumeratorize("count_to_3", ()))
    }
}

#[test]
fn it_converts_iterator_to_yields() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("count_to_3", method!(count_to_3, 0));

    let a = ruby.ary_new();
    let _: Value = eval!(
        ruby,
        "
        count_to_3 do |i|
          a << i
        end
        ",
        a
    )
    .unwrap();
    rb_assert!(ruby, "a == [1,2,3]", a);

    let enumerator: Value = eval!(
        ruby,
        "
        def raises
          yield
          false
        rescue StopIteration
          true
        end
        count_to_3
        "
    )
    .unwrap();
    rb_assert!(
        ruby,
        "enumerator.next == 1 && enumerator.next == 2 && enumerator.next == 3 && raises { enumerator.next }",
        enumerator
    );
}

use magnus::{
    block::{block_given, Yield},
    define_global_function, method, Value,
};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

fn count_to_3(rb_self: Value) -> Yield<impl Iterator<Item = u8>> {
    if block_given() {
        Yield::Iter((1..=3).into_iter())
    } else {
        Yield::Enumerator(rb_self.enumeratorize("count_to_3", ()))
    }
}

#[test]
fn it_converts_iterator_to_yields() {
    let _cleanup = unsafe { magnus::embed::init() };

    define_global_function("count_to_3", method!(count_to_3, 0));

    rb_assert!(
        "
    a = []
    count_to_3 do |i|
      a << i
    end
    a == [1,2,3]
    "
    );

    rb_assert!(
        "
    def raises
      yield
      false
    rescue StopIteration
      true
    end
    enum = count_to_3
    enum.next == 1 && enum.next == 2 && enum.next == 3 && raises { enum.next }
    "
    );
}

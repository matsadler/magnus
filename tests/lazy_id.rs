use magnus::{rb_assert, value::LazyId};

static FOO: LazyId = LazyId::new("foo");

#[test]
fn it_works() {
    let _ruby = unsafe { magnus::embed::init() };

    rb_assert!("foo == :foo", foo = *FOO);
}

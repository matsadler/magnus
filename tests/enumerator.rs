use magnus::{RArray, prelude::*};

#[test]
fn enumerator_impls_iterator() {
    let ruby = unsafe { magnus::embed::init() };
    let a: RArray = ruby.eval("[1,2,3]").unwrap();
    let mut e = a.enumeratorize("each", ());
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 1);
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 2);
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 3);
    assert!(e.next().is_none());
}

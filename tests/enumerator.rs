use magnus::{eval, prelude::*, RArray};

#[test]
fn enumerator_impls_iterator() {
    let _cleanup = unsafe { magnus::embed::init() };
    let a: RArray = eval("[1,2,3]").unwrap();
    let mut e = a.each();
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 1);
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 2);
    assert_eq!(e.next().unwrap().and_then(i64::try_convert).unwrap(), 3);
    assert!(e.next().is_none());
}

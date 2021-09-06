use magnus::{eval, RArray};

#[test]
fn enumerator_impls_iterator() {
    let _cleanup = unsafe { magnus::embed::init() };
    let a: RArray = eval("[1,2,3]").unwrap();
    let mut e = a.each();
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<i64>())
            .unwrap(),
        1
    );
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<i64>())
            .unwrap(),
        2
    );
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<i64>())
            .unwrap(),
        3
    );
    assert!(e.next().is_none());
}

use magnus::{eval, RArray};

#[test]
fn enumerator_impls_iterator() {
    let _cleanup = unsafe { magnus::embed::init() };
    let a: RArray = eval(r#"[1234,true,"Hello, world!"]"#).unwrap();
    let mut e = a.each();
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<i64>())
            .unwrap(),
        1234
    );
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<bool>())
            .unwrap(),
        true
    );
    assert_eq!(
        e.next()
            .unwrap()
            .and_then(|v| v.try_convert::<String>())
            .unwrap(),
        "Hello, world!"
    );
    assert!(e.next().is_none());
}

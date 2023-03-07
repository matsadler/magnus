use magnus::RArray;

#[test]
fn can_get_slice_from_r_attay() {
    let ruby = unsafe { magnus::embed::init() };

    let ary: RArray = ruby.eval(r#"[1, nil, "foo"]"#).unwrap();
    let slice = unsafe { ary.as_slice() };

    assert_eq!(3, slice.len());
    assert_eq!("1", format!("{:?}", slice[0]));
    assert_eq!("nil", format!("{:?}", slice[1]));
    assert_eq!(r#""foo""#, format!("{:?}", slice[2]));

    let ary: RArray = ruby
        .eval(r#"["bar", "baz", 42, [1, 2, 3], :test]"#)
        .unwrap();
    let slice = unsafe { ary.as_slice() };

    assert_eq!(5, slice.len());
    assert_eq!(r#""bar""#, format!("{:?}", slice[0]));
    assert_eq!(r#""baz""#, format!("{:?}", slice[1]));
    assert_eq!("42", format!("{:?}", slice[2]));
    assert_eq!("[1, 2, 3]", format!("{:?}", slice[3]));
    assert_eq!(":test", format!("{:?}", slice[4]));
}

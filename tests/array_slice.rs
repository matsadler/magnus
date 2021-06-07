use magnus::{eval_static, RArray};

#[test]
fn can_get_slice_from_r_attay() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = eval_static(r#"[1, nil, "foo"]"#).unwrap();
    let ary = unsafe { RArray::from_value(val).unwrap() };
    let slice = ary.as_slice();

    assert_eq!(3, slice.len());
    assert_eq!("1", format!("{:?}", slice[0]));
    assert_eq!("nil", format!("{:?}", slice[1]));
    assert_eq!(r#""foo""#, format!("{:?}", slice[2]));

    let val = eval_static(r#"["bar", "baz", 42, [1, 2, 3], :test]"#).unwrap();
    let ary = unsafe { RArray::from_value(val).unwrap() };
    let slice = ary.as_slice();

    assert_eq!(5, slice.len());
    assert_eq!(r#""bar""#, format!("{:?}", slice[0]));
    assert_eq!(r#""baz""#, format!("{:?}", slice[1]));
    assert_eq!("42", format!("{:?}", slice[2]));
    assert_eq!("[1, 2, 3]", format!("{:?}", slice[3]));
    assert_eq!(":test", format!("{:?}", slice[4]));
}

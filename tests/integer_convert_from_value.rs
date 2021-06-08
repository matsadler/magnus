#[test]
fn it_converts_integers_from_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    // in range
    let val = magnus::eval_static("-128").unwrap();
    let res = val.try_convert::<i8>();
    assert_eq!(res.unwrap(), -128);

    // out of range
    let val = magnus::eval_static("128").unwrap();
    let res = val.try_convert::<i8>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-32768").unwrap();
    let res = val.try_convert::<i16>();
    assert_eq!(res.unwrap(), -32768);

    // out of range
    let val = magnus::eval_static("32768").unwrap();
    let res = val.try_convert::<i16>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-2147483648").unwrap();
    let res = val.try_convert::<i32>();
    assert_eq!(res.unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("2147483648").unwrap();
    let res = val.try_convert::<i32>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-9223372036854775808").unwrap();
    let res = val.try_convert::<i64>();
    assert_eq!(res.unwrap(), -9223372036854775808);

    // out of range
    let val = magnus::eval_static("9223372036854775808").unwrap();
    let res = val.try_convert::<i64>();
    assert!(res.is_err());

    // in range (fixnum)
    let val = magnus::eval_static("4611686018427387903").unwrap();
    let res = val.try_convert::<i64>();
    assert_eq!(res.unwrap(), 4611686018427387903);

    // in range
    let val = magnus::eval_static("-2147483648").unwrap();
    let res = val.try_convert::<isize>();
    assert_eq!(res.unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("9223372036854775808").unwrap();
    let res = val.try_convert::<isize>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("255").unwrap();
    let res = val.try_convert::<u8>();
    assert_eq!(res.unwrap(), 255);

    // out of range
    let val = magnus::eval_static("256").unwrap();
    let res = val.try_convert::<u8>();
    assert!(res.is_err());

    let val = magnus::eval_static("-1").unwrap();
    let res = val.try_convert::<u8>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("65535").unwrap();
    let res = val.try_convert::<u16>();
    assert_eq!(res.unwrap(), 65535);

    // out of range
    let val = magnus::eval_static("65536").unwrap();
    let res = val.try_convert::<u16>();
    assert!(res.is_err());

    let val = magnus::eval_static("-1").unwrap();
    let res = val.try_convert::<u16>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").unwrap();
    let res = val.try_convert::<u32>();
    assert_eq!(res.unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("4294967296").unwrap();
    let res = val.try_convert::<u32>();
    assert!(res.is_err());

    let val = magnus::eval_static("-1").unwrap();
    let res = val.try_convert::<u32>();
    assert!(res.is_err());

    let val = magnus::eval_static("-2147483648").unwrap();
    let res = val.try_convert::<u32>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("18446744073709551615").unwrap();
    let res = val.try_convert::<u64>();
    assert_eq!(res.unwrap(), 18446744073709551615);

    // out of range
    let val = magnus::eval_static("18446744073709551616").unwrap();
    let res = val.try_convert::<u64>();
    assert!(res.is_err());

    let val = magnus::eval_static("-1").unwrap();
    let res = val.try_convert::<u64>();
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").unwrap();
    let res = val.try_convert::<u64>();
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").unwrap();
    let res = val.try_convert::<usize>();
    assert_eq!(res.unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("18446744073709551616").unwrap();
    let res = val.try_convert::<usize>();
    assert!(res.is_err());

    let val = magnus::eval_static("-1").unwrap();
    let res = val.try_convert::<usize>();
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").unwrap();
    let res = val.try_convert::<usize>();
    assert!(res.is_err());
}

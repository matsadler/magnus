#[test]
fn it_converts_integers_from_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    // in range
    let val = magnus::eval_static("-128").ok().unwrap();
    let res = unsafe { val.try_convert::<i8>() };
    assert_eq!(res.ok().unwrap(), -128);

    // out of range
    let val = magnus::eval_static("128").ok().unwrap();
    let res = unsafe { val.try_convert::<i8>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-32768").ok().unwrap();
    let res = unsafe { val.try_convert::<i16>() };
    assert_eq!(res.ok().unwrap(), -32768);

    // out of range
    let val = magnus::eval_static("32768").ok().unwrap();
    let res = unsafe { val.try_convert::<i16>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { val.try_convert::<i32>() };
    assert_eq!(res.ok().unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("2147483648").ok().unwrap();
    let res = unsafe { val.try_convert::<i32>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { val.try_convert::<i64>() };
    assert_eq!(res.ok().unwrap(), -9223372036854775808);

    // out of range
    let val = magnus::eval_static("9223372036854775808").ok().unwrap();
    let res = unsafe { val.try_convert::<i64>() };
    assert!(res.is_err());

    // in range (fixnum)
    let val = magnus::eval_static("4611686018427387903").ok().unwrap();
    let res = unsafe { val.try_convert::<i64>() };
    assert_eq!(res.ok().unwrap(), 4611686018427387903);

    // in range
    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { val.try_convert::<isize>() };
    assert_eq!(res.ok().unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("9223372036854775808").ok().unwrap();
    let res = unsafe { val.try_convert::<isize>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("255").ok().unwrap();
    let res = unsafe { val.try_convert::<u8>() };
    assert_eq!(res.ok().unwrap(), 255);

    // out of range
    let val = magnus::eval_static("256").ok().unwrap();
    let res = unsafe { val.try_convert::<u8>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { val.try_convert::<u8>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("65535").ok().unwrap();
    let res = unsafe { val.try_convert::<u16>() };
    assert_eq!(res.ok().unwrap(), 65535);

    // out of range
    let val = magnus::eval_static("65536").ok().unwrap();
    let res = unsafe { val.try_convert::<u16>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { val.try_convert::<u16>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").ok().unwrap();
    let res = unsafe { val.try_convert::<u32>() };
    assert_eq!(res.ok().unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("4294967296").ok().unwrap();
    let res = unsafe { val.try_convert::<u32>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { val.try_convert::<u32>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { val.try_convert::<u32>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("18446744073709551615").ok().unwrap();
    let res = unsafe { val.try_convert::<u64>() };
    assert_eq!(res.ok().unwrap(), 18446744073709551615);

    // out of range
    let val = magnus::eval_static("18446744073709551616").ok().unwrap();
    let res = unsafe { val.try_convert::<u64>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { val.try_convert::<u64>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { val.try_convert::<u64>() };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").ok().unwrap();
    let res = unsafe { val.try_convert::<usize>() };
    assert_eq!(res.ok().unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("18446744073709551616").ok().unwrap();
    let res = unsafe { val.try_convert::<usize>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { val.try_convert::<usize>() };
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { val.try_convert::<usize>() };
    assert!(res.is_err());
}

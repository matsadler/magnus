use magnus::prelude::*;

#[test]
fn it_converts_integers_from_value() {
    let _cleanup = unsafe { magnus::init() };

    // in range
    let val = magnus::eval_static("-128").ok().unwrap();
    let res = unsafe { i8::try_convert(val) };
    assert_eq!(res.ok().unwrap(), -128);

    // out of range
    let val = magnus::eval_static("128").ok().unwrap();
    let res = unsafe { i8::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-32768").ok().unwrap();
    let res = unsafe { i16::try_convert(val) };
    assert_eq!(res.ok().unwrap(), -32768);

    // out of range
    let val = magnus::eval_static("32768").ok().unwrap();
    let res = unsafe { i16::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { i32::try_convert(val) };
    assert_eq!(res.ok().unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("2147483648").ok().unwrap();
    let res = unsafe { i32::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { i64::try_convert(val) };
    assert_eq!(res.ok().unwrap(), -9223372036854775808);

    // out of range
    let val = magnus::eval_static("9223372036854775808").ok().unwrap();
    let res = unsafe { i64::try_convert(val) };
    assert!(res.is_err());

    // in range (fixnum)
    let val = magnus::eval_static("4611686018427387903").ok().unwrap();
    let res = unsafe { i64::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 4611686018427387903);

    // in range
    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { isize::try_convert(val) };
    assert_eq!(res.ok().unwrap(), -2147483648);

    // out of range
    let val = magnus::eval_static("9223372036854775808").ok().unwrap();
    let res = unsafe { isize::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("255").ok().unwrap();
    let res = unsafe { u8::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 255);

    // out of range
    let val = magnus::eval_static("256").ok().unwrap();
    let res = unsafe { u8::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { u8::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("65535").ok().unwrap();
    let res = unsafe { u16::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 65535);

    // out of range
    let val = magnus::eval_static("65536").ok().unwrap();
    let res = unsafe { u16::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { u16::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").ok().unwrap();
    let res = unsafe { u32::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("4294967296").ok().unwrap();
    let res = unsafe { u32::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { u32::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-2147483648").ok().unwrap();
    let res = unsafe { u32::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("18446744073709551615").ok().unwrap();
    let res = unsafe { u64::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 18446744073709551615);

    // out of range
    let val = magnus::eval_static("18446744073709551616").ok().unwrap();
    let res = unsafe { u64::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { u64::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { u64::try_convert(val) };
    assert!(res.is_err());

    // in range
    let val = magnus::eval_static("4294967295").ok().unwrap();
    let res = unsafe { usize::try_convert(val) };
    assert_eq!(res.ok().unwrap(), 4294967295);

    // out of range
    let val = magnus::eval_static("18446744073709551616").ok().unwrap();
    let res = unsafe { usize::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-1").ok().unwrap();
    let res = unsafe { usize::try_convert(val) };
    assert!(res.is_err());

    let val = magnus::eval_static("-9223372036854775808").ok().unwrap();
    let res = unsafe { usize::try_convert(val) };
    assert!(res.is_err());
}

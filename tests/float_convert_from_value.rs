#[test]
fn it_converts_floats_from_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = magnus::eval_static("1.0").unwrap();
    let res = val.try_convert::<f64>();
    assert_eq!(res.unwrap(), 1.0);

    let val = magnus::eval_static("1").unwrap();
    let res = val.try_convert::<f64>();
    assert_eq!(res.unwrap(), 1.0);

    let val = magnus::eval_static("1/2r").unwrap();
    let res = val.try_convert::<f64>();
    assert_eq!(res.unwrap(), 0.5);

    let val = magnus::eval_static("18446744073709551615").unwrap();
    let res = val.try_convert::<f64>();
    assert_eq!(res.unwrap(), 18446744073709552000.0);

    let val = magnus::eval_static(r#""1.0""#).unwrap();
    let res = val.try_convert::<f64>();
    assert!(res.is_err());

    let val = magnus::eval_static("Object.new").unwrap();
    let res = val.try_convert::<f64>();
    assert!(res.is_err());

    let val = magnus::eval_static("nil").unwrap();
    let res = val.try_convert::<f64>();
    assert!(res.is_err());

    let val = magnus::eval_static("Float::INFINITY").unwrap();
    let res = val.try_convert::<f64>();
    assert_eq!(res.unwrap(), f64::INFINITY);

    let val = magnus::eval_static("Float::NAN").unwrap();
    let res = val.try_convert::<f64>();
    assert!(res.unwrap().is_nan());
}

use magnus::prelude::*;

#[test]
fn it_converts_floats_from_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = magnus::eval::<magnus::Value>("1.0").unwrap();
    let res = f64::try_convert(val);
    assert_eq!(res.unwrap(), 1.0);

    let val = magnus::eval::<magnus::Value>("1").unwrap();
    let res = f64::try_convert(val);
    assert_eq!(res.unwrap(), 1.0);

    let val = magnus::eval::<magnus::Value>("1/2r").unwrap();
    let res = f64::try_convert(val);
    assert_eq!(res.unwrap(), 0.5);

    let val = magnus::eval::<magnus::Value>("18446744073709551615").unwrap();
    let res = f64::try_convert(val);
    assert_eq!(res.unwrap(), 18446744073709552000.0);

    let val = magnus::eval::<magnus::Value>(r#""1.0""#).unwrap();
    let res = f64::try_convert(val);
    assert!(res.is_err());

    let val = magnus::eval::<magnus::Value>("Object.new").unwrap();
    let res = f64::try_convert(val);
    assert!(res.is_err());

    let val = magnus::eval::<magnus::Value>("nil").unwrap();
    let res = f64::try_convert(val);
    assert!(res.is_err());

    let val = magnus::eval::<magnus::Value>("Float::INFINITY").unwrap();
    let res = f64::try_convert(val);
    assert_eq!(res.unwrap(), f64::INFINITY);

    let val = magnus::eval::<magnus::Value>("Float::NAN").unwrap();
    let res = f64::try_convert(val);
    assert!(res.unwrap().is_nan());
}

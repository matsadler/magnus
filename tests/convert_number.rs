use magnus::{Fixnum, RBignum};

#[test]
fn it_converts_numbers() {
    let _cleanup = unsafe { magnus::init() };

    let val = magnus::eval_static("-1").ok().unwrap();
    let i = Fixnum::from_value(&val).unwrap();
    assert_eq!(i.to_i64(), -1);

    let val = magnus::eval_static("-1").ok().unwrap();
    let i = Fixnum::from_value(&val).unwrap();
    assert!(i.to_u64().is_err());

    let val = magnus::eval_static("-4611686018427387905").ok().unwrap();
    unsafe {
        let i = RBignum::from_value(&val).unwrap();
        assert_eq!(i.to_i64().ok().unwrap(), -4611686018427387905);
    }

    let val = magnus::eval_static("-4611686018427387905").ok().unwrap();
    unsafe {
        let i = RBignum::from_value(&val).unwrap();
        assert!(i.to_u64().is_err());
    }
}

use magnus::{
    define_global_variable,
    r_struct::{define_struct, RStruct},
    QNIL,
};

macro_rules! rb_assert {
    ($eval:literal) => {
        assert!(magnus::eval::<bool>($eval).unwrap())
    };
}

#[test]
fn it_defines_a_struct() {
    let _cleanup = unsafe { magnus::embed::init() };
    let val = define_global_variable("$val", QNIL).unwrap();
    rb_assert!("$val == nil");

    let struct_class = define_struct(Some("Foo"), ("bar", "baz")).unwrap();

    unsafe { val.replace(struct_class.into()) };
    rb_assert!(r#"$val.name == "Struct::Foo""#);
    rb_assert!("$val.members == [:bar, :baz]");

    let obj = struct_class.new_instance((1, 2)).unwrap();

    unsafe { val.replace(obj.into()) };
    rb_assert!("$val.bar == 1");
    rb_assert!("$val.baz == 2");

    unsafe { val.replace(define_struct(None, ("foo",)).unwrap().into()) };
    rb_assert!(r#"$val.name == nil"#);

    let obj = RStruct::from_value(obj).unwrap();
    unsafe {
        if let &[bar, baz] = obj.as_slice() {
            assert_eq!(1, bar.try_convert::<usize>().unwrap());
            assert_eq!(2, baz.try_convert::<usize>().unwrap());
        } else {
            panic!()
        }
    }

    assert_eq!(&["bar", "baz"], obj.members().unwrap().as_slice())
}

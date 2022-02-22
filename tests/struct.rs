use magnus::{
    r_struct::{define_struct, RStruct},
};

macro_rules! rb_assert {
    ($s:literal) => {
        assert!(magnus::eval::<bool>($s).unwrap())
    };
    ($s:literal, $($rest:tt)*) => {
        let result: bool = magnus::eval!($s, $($rest)*).unwrap();
        assert!(result)
    };
}

#[test]
fn it_defines_a_struct() {
    let _cleanup = unsafe { magnus::embed::init() };

    let struct_class = define_struct(Some("Foo"), ("bar", "baz")).unwrap();

    rb_assert!(r#"val.name == "Struct::Foo""#, val = struct_class);
    rb_assert!("val.members == [:bar, :baz]", val = struct_class);

    let obj = struct_class.new_instance((1, 2)).unwrap();

    rb_assert!("val.bar == 1", val = obj);
    rb_assert!("val.baz == 2", val = obj);

    rb_assert!(r#"val.name == nil"#, val = define_struct(None, ("foo",)).unwrap());

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

use magnus::{RArray, Value};

#[test]
fn it_can_call_method_with_block() {
    let _cleanup = unsafe { magnus::embed::init() };

    let ary = RArray::from_slice(&[1.into(), 2.into(), 3.into()]);
    let _: Value = ary
        .block_call("map!", (), |args, _| {
            (args[0].try_convert::<i64>().unwrap() * 4).into()
        })
        .unwrap();

    assert_eq!(ary.to_vec::<i64>().unwrap(), vec![4, 8, 12]);
}

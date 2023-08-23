use magnus::{prelude::*, Value};

#[test]
fn it_can_call_method_with_block() {
    let ruby = unsafe { magnus::embed::init() };

    let ary = ruby.ary_new_from_values(&[
        ruby.into_value(1_i64),
        ruby.into_value(2_i64),
        ruby.into_value(3_i64),
    ]);
    let _: Value = ary
        .block_call("map!", (), |_, args, _| {
            i64::try_convert(args[0]).map(|i| i * 4)
        })
        .unwrap();

    assert_eq!(ary.to_vec::<i64>().unwrap(), vec![4, 8, 12]);
}

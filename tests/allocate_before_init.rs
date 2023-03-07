use magnus::eval;

// this will fail if the allocator calls Ruby, like with rb-sys's
// global-allocator feature
#[test]
fn can_allocate_before_ruby_init() {
    // allocate something
    let x: Vec<i64> = (0..256).collect();

    // *then* init Ruby
    let ruby = unsafe { magnus::embed::init() };

    // do something with allocated data to ensure it's not optimised away
    let res: i64 = eval!(ruby, "x.sum", x).unwrap();
    assert_eq!(res, 32640);
}

use magnus::{block::Proc, eval_static};

#[test]
fn it_calls_proc() {
    let _cleanup = unsafe { magnus::embed::init() };

    let val = eval_static("Proc.new {|i| i + 1}").unwrap();
    let p = Proc::from_value(val).unwrap();
    assert_eq!(43, p.call((42,)).unwrap());
}

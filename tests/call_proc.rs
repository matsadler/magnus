use magnus::{block::Proc, eval};

#[test]
fn it_calls_proc() {
    let _cleanup = unsafe { magnus::embed::init() };

    let p: Proc = eval("Proc.new {|i| i + 1}").unwrap();
    assert_eq!(43, p.call((42,)).unwrap());
}

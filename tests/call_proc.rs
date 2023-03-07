use magnus::block::Proc;

#[test]
fn it_calls_proc() {
    let ruby = unsafe { magnus::embed::init() };

    let p: Proc = ruby.eval("Proc.new {|i| i + 1}").unwrap();
    assert_eq!(43, p.call((42,)).unwrap());
}

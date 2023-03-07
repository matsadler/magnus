use magnus::{block::Proc, eval, Ruby};

fn make_proc(ruby: &Ruby) -> Proc {
    let x = String::from("foo");
    ruby.proc_from_fn(move |_args, _block| Ok(x.clone()))
}

#[test]
fn proc_from_closure_can_be_called_later() {
    let ruby = unsafe { magnus::embed::init() };

    let proc = make_proc(&ruby);

    let res: bool = eval!(ruby, r#"proc.call == "foo""#, proc).unwrap();
    assert!(res);
}

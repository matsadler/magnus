use magnus::{block::Proc, eval};

fn make_proc() -> Proc {
    let x = String::from("foo");
    Proc::new(move |_args, _block| Ok(x.clone()))
}

#[test]
fn proc_from_closure_can_be_called_later() {
    let _cleanup = unsafe { magnus::embed::init() };

    let proc = make_proc();

    let res: bool = eval!(r#"proc.call == "foo""#, proc).unwrap();
    assert!(res);
}

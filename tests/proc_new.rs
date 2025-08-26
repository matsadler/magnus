use magnus::{Ruby, Value, block::Proc, eval, value::Opaque};

fn make_proc(ruby: &Ruby) -> Proc {
    let x = String::from("foo");
    let y = Opaque::from(ruby.str_new("bar"));
    ruby.proc_from_fn(move |_ruby, _args, _block| Ok((x.clone(), y)))
}

#[test]
fn proc_from_closure_can_be_called_later() {
    let ruby = unsafe { magnus::embed::init() };

    let proc = make_proc(&ruby);

    eval::<Value>(r#"1024.times.map {|i| "test#{i}"}"#).unwrap();

    ruby.gc_start();

    let res: bool = eval!(ruby, r#"proc.call == ["foo", "bar"]"#, proc).unwrap();
    assert!(res);
}

use magnus::{
    RArray, RHash, Ruby, Symbol,
    block::Proc,
    error::Error,
    method,
    scan_args::{get_kwargs, scan_args},
    value::Value,
};

fn example(ruby: &Ruby, _rb_self: Value, args: &[Value]) -> Result<RArray, Error> {
    let args = scan_args(args)?;
    let (a,): (String,) = args.required;
    let (b,): (Option<String>,) = args.optional;
    let splat: RArray = args.splat;
    let (c,): (Symbol,) = args.trailing;
    let kw = get_kwargs::<_, (usize,), (Option<usize>, Option<usize>, Option<usize>), RHash>(
        args.keywords,
        &["d"],
        &["e", "f", "g"],
    )?;
    let (d,) = kw.required;
    let (e, f, g) = kw.optional;
    let kw_splat = kw.splat;
    let _: Option<Proc> = args.block;

    let res = ruby.ary_new_capa(7);
    res.push(a)?;
    res.push(b)?;
    res.push(splat)?;
    res.push(c)?;
    res.push(d)?;
    if let Some(e) = e {
        res.push(e)?;
    }
    res.push(f)?;
    if let Some(g) = g {
        res.push(g)?;
    }
    res.push(kw_splat)?;
    Ok(res)
}

#[test]
fn it_scans_args() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.define_global_function("example", method!(example, -1));

    let res = ruby.eval::<bool>(r#"
        example("a", "b", "splat1", "splat2", :c, d: 1, f: 2, h: 3) == ["a", "b", ["splat1", "splat2"], :c, 1, 2, {h: 3}]
    "#).unwrap();
    assert!(res);

    let res = ruby
        .eval::<bool>(
            r#"
        example("a", :c, d: 1) == ["a", nil, [], :c, 1, nil, {}]
    "#,
        )
        .unwrap();
    assert!(res);
}

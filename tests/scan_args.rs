use magnus::{
    block::Proc,
    define_global_function,
    error::Error,
    eval, method,
    scan_args::{get_kwargs, scan_args},
    value::Value,
    RArray, RHash, Symbol,
};

fn example(_rb_self: Value, args: &[Value]) -> Result<RArray, Error> {
    let args = scan_args(args)?;
    let (a,): (String,) = args.required;
    let (b,): (Option<String>,) = args.optional;
    let splat: RArray = args.splat;
    let (c,): (Symbol,) = args.trailing;
    let kw = get_kwargs::<_, (usize,), (Option<usize>,), RHash>(args.keywords, &["d"], &["e"])?;
    let (d,) = kw.required;
    let (e,) = kw.optional;
    let kw_splat = kw.splat;
    let _: Option<Proc> = args.block;

    let res = RArray::with_capacity(7);
    res.push(a)?;
    res.push(b)?;
    res.push(splat)?;
    res.push(c)?;
    res.push(d)?;
    res.push(e)?;
    res.push(kw_splat)?;
    Ok(res)
}

#[test]
fn it_scans_args() {
    let _cleanup = unsafe { magnus::embed::init() };

    define_global_function("example", method!(example, -1));

    let res = eval::<bool>(r#"
        example("a", "b", "splat1", "splat2", :c, d: 1, e: 2, f: 3) == ["a", "b", ["splat1", "splat2"], :c, 1, 2, {f: 3}]
    "#).unwrap();
    assert!(res);

    let res = eval::<bool>(
        r#"
        example("a", :c, d: 1) == ["a", nil, [], :c, 1, nil, {}]
    "#,
    )
    .unwrap();
    assert!(res);
}

#[test]
fn it_converts_to_bytes() {
    use magnus::RString;

    let ruby = unsafe { magnus::embed::init() };

    let s: RString = ruby.eval("[0,0,0].pack('c*')").unwrap();
    assert_eq!(bytes::Bytes::from_static(&[0, 0, 0]), s.to_bytes());
}

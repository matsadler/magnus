#[test]
#[cfg(feature = "bytes-crate")]
fn it_converts_to_bytes() {
    use magnus::{eval, RString};

    let _cleanup = unsafe { magnus::embed::init() };

    let s: RString = unsafe { eval("[0,0,0].pack('c*')").unwrap() };
    assert_eq!(bytes::Bytes::from_static(&[0, 0, 0]), s.to_bytes());
}

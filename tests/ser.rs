use magnus::{value::serialize, Integer, RArray, RHash, RString, Symbol};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct A {
    b: B,
    c: [i32; 3],
    d: Option<D>,
}

#[derive(Serialize, Deserialize)]
struct B(u32);

#[derive(Serialize, Deserialize)]
enum D {
    A { a: String },
}

#[test]
fn it_serializes_a_rust_type_to_a_ruby_value() {
    let _cleanup = unsafe { magnus::embed::init() };

    let a = A {
        b: B(1234),
        c: [123, -456, 789],
        d: Some(D::A {
            a: String::from("test"),
        }),
    };

    let a_as_hash = serialize::<A, RHash>(&a).unwrap();

    let b: Integer = a_as_hash.lookup(Symbol::new("b")).unwrap();
    assert_eq!(1234, b.to_u32().unwrap());

    let c: RArray = a_as_hash.lookup(Symbol::new("c")).unwrap();
    assert_eq!(3, c.len());
    assert_eq!(123, c.entry::<Integer>(0).unwrap().to_i32().unwrap());
    assert_eq!(-456, c.entry::<Integer>(1).unwrap().to_i32().unwrap());
    assert_eq!(789, c.entry::<Integer>(2).unwrap().to_i32().unwrap());

    let d: RHash = a_as_hash.lookup(Symbol::new("d")).unwrap();
    let d: RHash = d.lookup("A").unwrap();
    let d_a: RString = d.lookup(Symbol::new("a")).unwrap();
    assert_eq!("test", d_a.to_string().unwrap());
}

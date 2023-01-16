use magnus::{eval, value::deserialize, Value};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
struct A {
    b: B,
    c: [i32; 3],
    d: Option<D>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct B(u32);

#[derive(Serialize, Deserialize, PartialEq, Debug)]
enum D {
    A { a: String },
}

#[test]
fn it_deserializes_a_ruby_value_to_a_rust_type() {
    let _cleanup = unsafe { magnus::embed::init() };

    let a_as_hash: Value = eval(
        r#"
        {
          b: 1234,
          c: [123, -456, 789],
          d: {
            "A" => { a: "test" }
          }
        }
        "#,
    )
    .unwrap();

    let a: A = deserialize(a_as_hash).unwrap();

    assert_eq!(B(1234), a.b);
    assert_eq!([123, -456, 789], a.c);
    assert_eq!(
        Some(D::A {
            a: String::from("test")
        }),
        a.d
    );
}

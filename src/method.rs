use std::{ffi::c_void, os::raw::c_int};

use crate::{r_array::RArray, value::Value};

pub trait Method {
    fn arity() -> i8;
    #[allow(clippy::wrong_self_convention)]
    fn as_ptr(self) -> *mut c_void;
}

impl Method for unsafe extern "C" fn(Value, RArray) -> Value {
    fn arity() -> i8 {
        -2
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(c_int, *const Value, Value) -> Value {
    fn arity() -> i8 {
        -1
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value) -> Value {
    fn arity() -> i8 {
        0
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value) -> Value {
    fn arity() -> i8 {
        1
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value, Value) -> Value {
    fn arity() -> i8 {
        2
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value, Value, Value) -> Value {
    fn arity() -> i8 {
        3
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value, Value, Value, Value) -> Value {
    fn arity() -> i8 {
        4
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value, Value, Value, Value, Value) -> Value {
    fn arity() -> i8 {
        5
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method for unsafe extern "C" fn(Value, Value, Value, Value, Value, Value, Value) -> Value {
    fn arity() -> i8 {
        6
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(Value, Value, Value, Value, Value, Value, Value, Value) -> Value
{
    fn arity() -> i8 {
        7
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(Value, Value, Value, Value, Value, Value, Value, Value, Value) -> Value
{
    fn arity() -> i8 {
        8
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        9
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        10
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        11
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        12
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        13
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        14
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        15
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

impl Method
    for unsafe extern "C" fn(
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
        Value,
    ) -> Value
{
    fn arity() -> i8 {
        16
    }

    fn as_ptr(self) -> *mut c_void {
        self as *mut c_void
    }
}

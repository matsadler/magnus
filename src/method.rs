#![allow(clippy::too_many_arguments)]
#![allow(clippy::many_single_char_names)]
#![allow(clippy::missing_safety_doc)]

use std::{ffi::c_void, marker::PhantomData, os::raw::c_int, panic::AssertUnwindSafe, slice};

use crate::{
    error::{raise, Error},
    r_array::RArray,
    try_convert::TryConvert,
    value::Value,
};

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

pub struct MethodRbAry<Func, RbSelf, Args, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    args: PhantomData<Args>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, Args, Res> MethodRbAry<Func, RbSelf, Args, Res>
where
    Func: Fn(RbSelf, Args) -> Result<Res, Error>,
    RbSelf: TryConvert,
    Args: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            args: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(self, rb_self: Value, args: RArray) -> Result<Value, Error> {
        (self.func)(rb_self.try_convert()?, args.try_convert()?).map(Into::into)
    }

    pub unsafe fn call_handle_error(self, rb_self: Value, args: RArray) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, args)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct MethodCAry<Func, RbSelf, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, Res> MethodCAry<Func, RbSelf, Res>
where
    Func: Fn(RbSelf, &[Value]) -> Result<Res, Error>,
    RbSelf: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Result<Value, Error> {
        let args = slice::from_raw_parts(argv, argc as usize);
        (self.func)(rb_self.try_convert()?, args).map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        argc: c_int,
        argv: *const Value,
        rb_self: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(argc, argv, rb_self)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method0<Func, RbSelf, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,

    res: PhantomData<Res>,
}

impl<Func, RbSelf, Res> Method0<Func, RbSelf, Res>
where
    Func: Fn(RbSelf) -> Result<Res, Error>,
    RbSelf: TryConvert,

    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),

            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(self, rb_self: Value) -> Result<Value, Error> {
        (self.func)(rb_self.try_convert()?).map(Into::into)
    }

    pub unsafe fn call_handle_error(self, rb_self: Value) -> Value {
        let res =
            match std::panic::catch_unwind(AssertUnwindSafe(|| self.call_convert_value(rb_self))) {
                Ok(v) => v,
                Err(e) => Err(Error::from_panic(e)),
            };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method1<Func, RbSelf, A, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, Res> Method1<Func, RbSelf, A, Res>
where
    Func: Fn(RbSelf, A) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(self, rb_self: Value, a: Value) -> Result<Value, Error> {
        (self.func)(rb_self.try_convert()?, a.try_convert()?).map(Into::into)
    }

    pub unsafe fn call_handle_error(self, rb_self: Value, a: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method2<Func, RbSelf, A, B, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, Res> Method2<Func, RbSelf, A, B, Res>
where
    Func: Fn(RbSelf, A, B) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(self, rb_self: Value, a: Value, b: Value) -> Result<Value, Error> {
        (self.func)(rb_self.try_convert()?, a.try_convert()?, b.try_convert()?).map(Into::into)
    }

    pub unsafe fn call_handle_error(self, rb_self: Value, a: Value, b: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method3<Func, RbSelf, A, B, C, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, Res> Method3<Func, RbSelf, A, B, C, Res>
where
    Func: Fn(RbSelf, A, B, C) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(self, rb_self: Value, a: Value, b: Value, c: Value) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method4<Func, RbSelf, A, B, C, D, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, Res> Method4<Func, RbSelf, A, B, C, D, Res>
where
    Func: Fn(RbSelf, A, B, C, D) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method5<Func, RbSelf, A, B, C, D, E, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, Res> Method5<Func, RbSelf, A, B, C, D, E, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method6<Func, RbSelf, A, B, C, D, E, F, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, Res> Method6<Func, RbSelf, A, B, C, D, E, F, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method7<Func, RbSelf, A, B, C, D, E, F, G, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, Res> Method7<Func, RbSelf, A, B, C, D, E, F, G, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method8<Func, RbSelf, A, B, C, D, E, F, G, H, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, Res> Method8<Func, RbSelf, A, B, C, D, E, F, G, H, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method9<Func, RbSelf, A, B, C, D, E, F, G, H, I, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, Res>
    Method9<Func, RbSelf, A, B, C, D, E, F, G, H, I, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method10<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, Res>
    Method10<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method11<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, Res>
    Method11<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method12<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    l: PhantomData<L>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, Res>
    Method12<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K, L) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    L: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            l: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
            l.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k, l)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method13<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    l: PhantomData<L>,
    m: PhantomData<M>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, Res>
    Method13<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    L: TryConvert,
    M: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            l: Default::default(),
            m: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
            l.try_convert()?,
            m.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method14<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    l: PhantomData<L>,
    m: PhantomData<M>,
    n: PhantomData<N>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, Res>
    Method14<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    L: TryConvert,
    M: TryConvert,
    N: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            l: Default::default(),
            m: Default::default(),
            n: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
            l.try_convert()?,
            m.try_convert()?,
            n.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method15<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    l: PhantomData<L>,
    m: PhantomData<M>,
    n: PhantomData<N>,
    o: PhantomData<O>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, Res>
    Method15<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    L: TryConvert,
    M: TryConvert,
    N: TryConvert,
    O: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            l: Default::default(),
            m: Default::default(),
            n: Default::default(),
            o: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
        o: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
            l.try_convert()?,
            m.try_convert()?,
            n.try_convert()?,
            o.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
        o: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

pub struct Method16<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Res> {
    func: Func,
    rb_self: PhantomData<RbSelf>,
    a: PhantomData<A>,
    b: PhantomData<B>,
    c: PhantomData<C>,
    d: PhantomData<D>,
    e: PhantomData<E>,
    f: PhantomData<F>,
    g: PhantomData<G>,
    h: PhantomData<H>,
    i: PhantomData<I>,
    j: PhantomData<J>,
    k: PhantomData<K>,
    l: PhantomData<L>,
    m: PhantomData<M>,
    n: PhantomData<N>,
    o: PhantomData<O>,
    p: PhantomData<P>,
    res: PhantomData<Res>,
}

impl<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Res>
    Method16<Func, RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Res>
where
    Func: Fn(RbSelf, A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P) -> Result<Res, Error>,
    RbSelf: TryConvert,
    A: TryConvert,
    B: TryConvert,
    C: TryConvert,
    D: TryConvert,
    E: TryConvert,
    F: TryConvert,
    G: TryConvert,
    H: TryConvert,
    I: TryConvert,
    J: TryConvert,
    K: TryConvert,
    L: TryConvert,
    M: TryConvert,
    N: TryConvert,
    O: TryConvert,
    P: TryConvert,
    Res: Into<Value>,
{
    pub fn new(func: Func) -> Self {
        Self {
            func,
            rb_self: Default::default(),
            a: Default::default(),
            b: Default::default(),
            c: Default::default(),
            d: Default::default(),
            e: Default::default(),
            f: Default::default(),
            g: Default::default(),
            h: Default::default(),
            i: Default::default(),
            j: Default::default(),
            k: Default::default(),
            l: Default::default(),
            m: Default::default(),
            n: Default::default(),
            o: Default::default(),
            p: Default::default(),
            res: Default::default(),
        }
    }

    unsafe fn call_convert_value(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
        o: Value,
        p: Value,
    ) -> Result<Value, Error> {
        (self.func)(
            rb_self.try_convert()?,
            a.try_convert()?,
            b.try_convert()?,
            c.try_convert()?,
            d.try_convert()?,
            e.try_convert()?,
            f.try_convert()?,
            g.try_convert()?,
            h.try_convert()?,
            i.try_convert()?,
            j.try_convert()?,
            k.try_convert()?,
            l.try_convert()?,
            m.try_convert()?,
            n.try_convert()?,
            o.try_convert()?,
            p.try_convert()?,
        )
        .map(Into::into)
    }

    pub unsafe fn call_handle_error(
        self,
        rb_self: Value,
        a: Value,
        b: Value,
        c: Value,
        d: Value,
        e: Value,
        f: Value,
        g: Value,
        h: Value,
        i: Value,
        j: Value,
        k: Value,
        l: Value,
        m: Value,
        n: Value,
        o: Value,
        p: Value,
    ) -> Value {
        let res = match std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.call_convert_value(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
        })) {
            Ok(v) => v,
            Err(e) => Err(Error::from_panic(e)),
        };
        match res {
            Ok(v) => v,
            Err(e) => raise(e),
        }
    }
}

#[macro_export]
macro_rules! method {
    ($name:ident, -2) => {{
        unsafe extern "C" fn anon(rb_self: Value, args: RArray) -> Value {
            MethodRbAry::new($name).call_handle_error(rb_self, args)
        }
        anon as unsafe extern "C" fn(Value, RArray) -> Value
    }};
    ($name:ident, -1) => {{
        unsafe extern "C" fn anon(argc: c_int, argv: *const Value, rb_self: Value) -> Value {
            MethodCAry::new($name).call_handle_error(argc, argv, rb_self)
        }
        anon as unsafe extern "C" fn(c_int, *const Value, Value) -> Value
    }};
    ($name:ident, 0) => {{
        unsafe extern "C" fn anon(rb_self: Value) -> Value {
            magnus::method::Method0::new($name).call_handle_error(rb_self)
        }
        anon as unsafe extern "C" fn(Value) -> Value
    }};
    ($name:ident, 1) => {{
        unsafe extern "C" fn anon(rb_self: Value, a: Value) -> Value {
            magnus::method::Method1::new($name).call_handle_error(rb_self, a)
        }
        anon as unsafe extern "C" fn(Value, Value) -> Value
    }};
    ($name:ident, 2) => {{
        unsafe extern "C" fn anon(rb_self: Value, a: Value, b: Value) -> Value {
            magnus::method::Method2::new($name).call_handle_error(rb_self, a, b)
        }
        anon as unsafe extern "C" fn(Value, Value, Value) -> Value
    }};
    ($name:ident, 3) => {{
        unsafe extern "C" fn anon(rb_self: Value, a: Value, b: Value, c: Value) -> Value {
            magnus::method::Method3::new($name).call_handle_error(rb_self, a, b, c)
        }
        anon as unsafe extern "C" fn(Value, Value, Value, Value) -> Value
    }};
    ($name:ident, 4) => {{
        unsafe extern "C" fn anon(rb_self: Value, a: Value, b: Value, c: Value, d: Value) -> Value {
            magnus::method::Method4::new($name).call_handle_error(rb_self, a, b, c, d)
        }
        anon as unsafe extern "C" fn(Value, Value, Value, Value, Value) -> Value
    }};
    ($name:ident, 5) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
        ) -> Value {
            magnus::method::Method5::new($name).call_handle_error(rb_self, a, b, c, d, e, f)
        }
        anon as unsafe extern "C" fn(Value, Value, Value, Value, Value, Value) -> Value
    }};
    ($name:ident, 6) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
        ) -> Value {
            magnus::method::Method6::new($name).call_handle_error(rb_self, a, b, c, d, e, f)
        }
        anon as unsafe extern "C" fn(Value, Value, Value, Value, Value, Value, Value) -> Value
    }};
    ($name:ident, 7) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
        ) -> Value {
            magnus::method::Method7::new($name).call_handle_error(rb_self, a, b, c, d, e, f, g)
        }
        anon as unsafe extern "C" fn(
            Value,
            Value,
            Value,
            Value,
            Value,
            Value,
            Value,
            Value,
        ) -> Value
    }};
    ($name:ident, 8) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
        ) -> Value {
            magnus::method::Method8::new($name).call_handle_error(rb_self, a, b, c, d, e, f, g, h)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 9) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
        ) -> Value {
            magnus::method::Method9::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 10) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
        ) -> Value {
            magnus::method::Method10::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 11) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
        ) -> Value {
            magnus::method::Method11::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 12) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
            l: Value,
        ) -> Value {
            magnus::method::Method12::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 13) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
            l: Value,
            m: Value,
        ) -> Value {
            magnus::method::Method13::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 14) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
            l: Value,
            m: Value,
            n: Value,
        ) -> Value {
            magnus::method::Method14::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 15) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
            l: Value,
            m: Value,
            n: Value,
            o: Value,
        ) -> Value {
            magnus::method::Method15::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, 16) => {{
        unsafe extern "C" fn anon(
            rb_self: Value,
            a: Value,
            b: Value,
            c: Value,
            d: Value,
            e: Value,
            f: Value,
            g: Value,
            h: Value,
            i: Value,
            j: Value,
            k: Value,
            l: Value,
            m: Value,
            n: Value,
            o: Value,
            p: Value,
        ) -> Value {
            magnus::method::Method16::new($name)
                .call_handle_error(rb_self, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
        }
        anon as unsafe extern "C" fn(
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
    }};
    ($name:ident, $arity:expr) => {
        compile_error!("arity must be an integer literal between -2..=16")
    };
}

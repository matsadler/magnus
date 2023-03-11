use std::{
    cell::RefCell,
    io::{stdout, Stdout, Write},
};

use magnus::{class, define_class, exception, function, method, prelude::*, Error, RString};

#[magnus::wrap(class = "WordSink")]
struct WordSink {
    started: RefCell<bool>,
    sink: RefCell<Stdout>,
}

impl WordSink {
    fn new() -> Self {
        Self {
            started: RefCell::new(false),
            sink: RefCell::new(stdout()),
        }
    }

    fn concat(&self, s: RString) -> Result<usize, Error> {
        let mut sink = self.sink.borrow_mut();
        if *self.started.borrow() {
            let _ = sink.write(b" ");
        } else {
            *self.started.borrow_mut() = true;
        }
        let res = unsafe { sink.write(s.as_slice()) };
        res.map_err(|e| Error::new(exception::io_error(), e.to_string()))
    }
}

pub fn init() -> Result<(), Error> {
    let class = define_class("WordSink", class::object())?;
    class.define_singleton_method("new", function!(WordSink::new, 0))?;
    class.define_method("<<", method!(WordSink::concat, 1))?;
    Ok(())
}

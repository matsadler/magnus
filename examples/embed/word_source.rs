use std::io::{stdin, BufRead, Stdin};

use magnus::{
    block::yield_value, class, define_class, function, method, prelude::*, Error, RString, Value,
};

#[magnus::wrap(class = "WordSource")]
struct WordSource {
    source: Stdin,
}

impl WordSource {
    fn new() -> Self {
        Self { source: stdin() }
    }

    fn each(&self) -> Result<(), Error> {
        let mut source = self.source.lock();
        let mut buf = Vec::new();
        while let Ok(read) = source.read_until(b' ', &mut buf) {
            if read == 0 {
                break;
            }
            if buf[read - 1] == b' ' {
                buf.pop();
            }
            if !buf.is_empty() {
                let _: Value = yield_value(RString::from_slice(&buf))?;
            }
            buf.clear()
        }
        Ok(())
    }
}

pub fn init() -> Result<(), Error> {
    let class = define_class("WordSource", class::object())?;
    class.define_singleton_method("new", function!(WordSource::new, 0))?;
    class.define_method("each", method!(WordSource::each, 0))?;
    Ok(())
}

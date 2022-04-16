use magnus::{define_class, encoding::RbEncoding, method, prelude::*, Error, RString};

fn is_blank(s: &str) -> bool {
    !s.contains(|c: char| !c.is_whitespace())
}

fn rb_is_blank(rb_self: RString) -> Result<bool, Error> {
    // RString::as_str is unsafe as it's possible for Ruby to invalidate the
    // str as we hold a reference to it, but here we're only ever using the
    // &str before Ruby is invoked again, so it doesn't get a chance to mess
    // with it and this is safe.
    unsafe {
        match rb_self.as_str() {
            Ok(s) => Ok(is_blank(s)),
            Err(_) => Ok(is_blank(rb_self.conv_enc(RbEncoding::utf8())?.as_str()?)),
        }
    }
}

#[magnus::init]
fn init() -> Result<(), Error> {
    let class = define_class("String", Default::default())?;
    class.define_method("blank?", method!(rb_is_blank, 0));
    Ok(())
}

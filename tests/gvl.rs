use magnus::{Ruby, error::RubyUnavailableError};

#[test]
fn it_can_modify_gvl() {
    let ruby = unsafe { magnus::embed::init() };

    ruby.without_gvl(|| {
        assert!(matches!(
            Ruby::get(),
            Err(RubyUnavailableError::GvlUnlocked)
        ));

        Ruby::with_gvl(|_| {
            assert!(Ruby::get().is_ok());
        });
    });

    Ruby::with_gvl(|_| {
        assert!(Ruby::get().is_ok());
    });
}

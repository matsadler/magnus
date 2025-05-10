use magnus::{
    encoding::Index, io::*, value::ReprValue, Error, Fixnum, IntoValue, Module, Ruby, TryConvert,
};

#[test]
fn test_io_all() {
    magnus::Ruby::init(|ruby| {
        test_io_extract_modeenc_extracts_open_flags(ruby)?;
        test_io_extract_modeenc_extracts_fmode_flags(ruby)?;
        test_io_extract_modeenc_extracts_io_encoding(ruby)?;
        Ok(())
    })
    .unwrap();
}

fn run_io_extract_modeenc(
    ruby: &Ruby,
    mode: &str,
) -> Result<(OpenFlags, FMode, IoEncoding), Error> {
    let mut mode = ruby.str_new(mode).into_value_with(&ruby);
    let mut permission = ruby.qnil().into_value_with(&ruby);
    let kwargs = ruby.hash_new();
    let _ = kwargs.aset(ruby.to_symbol("encoding"), "GBK:UTF-8"); // follows "extern:intern". read more on `IO::new`
    ruby.io_extract_modeenc(&mut mode, &mut permission, &kwargs)
}

fn test_io_extract_modeenc_extracts_open_flags(ruby: &Ruby) -> Result<(), Error> {
    let (open_flags, _, _) = run_io_extract_modeenc(&ruby, "a")?;

    let file_class = ruby.class_file();
    let append_flag = file_class.const_get::<_, Fixnum>("APPEND")?.to_i32()?;

    assert!(open_flags.contains(append_flag));
    Ok(())
}

fn test_io_extract_modeenc_extracts_fmode_flags(ruby: &Ruby) -> Result<(), Error> {
    let (_, fmode_flags, _) = run_io_extract_modeenc(&ruby, "a")?;

    assert!(fmode_flags.contains(FMode::APPEND));
    assert!(fmode_flags.contains(FMode::READ_WRITE));
    assert!(fmode_flags.contains(FMode::CREATE));

    Ok(())
}

fn test_io_extract_modeenc_extracts_io_encoding(ruby: &Ruby) -> Result<(), Error> {
    let (_, _, io_encoding) = run_io_extract_modeenc(&ruby, "a")?;

    assert!(io_encoding.internal.is_some());
    assert!(io_encoding.external.is_some());

    let internal_index = Index::from(io_encoding.internal.unwrap());
    let external_index = Index::from(io_encoding.external.unwrap());
    let utf_8 = ruby.utf8_encindex();
    let gbk = Index::try_convert(ruby.str_new("GBK").as_value())?;

    assert!(internal_index == utf_8, "Internal encoding is not UTF-8");
    assert!(external_index == gbk, "External encoding is not GBK");

    Ok(())
}

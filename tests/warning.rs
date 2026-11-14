use magnus::{Error, Ruby, Value, prelude::*};

#[test]
fn warning_prints_percent_sequences_literally() {
    Ruby::init(|ruby| -> Result<(), Error> {
        let stderr: Value =
            ruby.eval("require 'stringio'; $VERBOSE = true; $stderr = StringIO.new")?;

        ruby.warning("100%% complete");

        let output: String = stderr.funcall("string", ())?;
        assert!(
            output.contains("100%% complete"),
            "warning changed literal text: {output}"
        );
        Ok(())
    })
    .unwrap();
}

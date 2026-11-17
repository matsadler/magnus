# frozen_string_literal: true

require "mkmf"
require "rb_sys/mkmf"

create_rust_makefile("jiff_magnus/jiff_magnus") do |config|
  config.extra_cargo_args << "--crate-type=cdylib"
end

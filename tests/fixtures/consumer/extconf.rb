# frozen_string_literal: true

require "mkmf"
require "rb_sys/mkmf"

create_rust_makefile("magnus_consumer") do |builder|
  builder.profile = :dev
  builder.use_stable_api_compiled_fallback = false
  builder.extra_cargo_args = ["--locked"]
  if ENV.fetch("MAGNUS_CONSUMER_FEATURES") == "minimal"
    builder.extra_cargo_args << "--no-default-features"
  end
end

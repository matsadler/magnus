# frozen_string_literal: true

require "rbconfig"
require "shellwords"
require "tmpdir"

target = File.join(__dir__, "target")
make = Shellwords.split(ENV.fetch("MAKE", RbConfig::CONFIG["MAKE"] || "make"))

# A caller's fallback overrides must not hide a regression in Magnus's own
# dependency features. No direct rb-sys dependency is present in the fixture.
build_env = {
  "RB_SYS_STABLE_API_COMPILED_FALLBACK" => nil,
  "RB_SYS_STABLE_API_COMPILED_FORCE" => nil
}

["default", "minimal"].each do |features|
  puts "Consumer features: #{features}"
  env = build_env.merge("MAGNUS_CONSUMER_FEATURES" => features)
  Dir.mktmpdir("magnus-consumer-") do |dir|
    # Use the same linker configuration as an extension gem on each platform.
    system(env, RbConfig.ruby, File.join(__dir__, "extconf.rb"), "--srcdir=#{__dir__}",
      chdir: dir, exception: true)
    system(env, *make, "RB_SYS_CARGO_TARGET_DIR=#{target}", chdir: dir, exception: true)
    extension = File.join(dir, "magnus_consumer.#{RbConfig::CONFIG.fetch('DLEXT')}")
    system(RbConfig.ruby, File.join(__dir__, "test.rb"), extension, exception: true)
  end
end

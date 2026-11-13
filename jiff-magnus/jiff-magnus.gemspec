# frozen_string_literal: true

Gem::Specification.new do |spec|
  spec.name = "jiff-magnus"
  manifest = File.read(File.join(__dir__, "Cargo.toml"))
  spec.version = manifest[/^version = "([^"]+)"$/, 1]
  spec.authors = ["Erick Guan"]
  spec.summary = "Jiff timezone rules and bundled timezone data for Ruby Time."
  spec.description = "A Magnus companion providing JiffTimezone constructors " \
                     "and bundled IANA timezone data for Ruby Time."
  spec.homepage = "https://github.com/matsadler/magnus"
  spec.license = "MIT"
  spec.required_ruby_version = ">= 3.2"
  spec.require_paths = ["lib"]
  spec.extensions = ["extconf.rb"]
  spec.files = Dir.chdir(__dir__) do
    Dir["lib/**/*.rb", "src/**/*.rs", "extconf.rb", "Cargo.toml",
        "README.md", "LICENSE", ".gitignore", "tmp/.gitignore"].sort
  end
  spec.metadata["source_code_uri"] = "https://github.com/matsadler/magnus/tree/main/jiff-magnus"
  spec.add_dependency "rb_sys", "~> 0.9.130"
end

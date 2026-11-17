# jiff-magnus

[jiff-magnus](https://rubygems.org/gems/jiff-magnus) provides Jiff timezones for
Ruby `Time` and bundles IANA timezone data.

## Install and use

```sh
gem install jiff-magnus
```

```ruby
require "jiff_magnus"

zone = JiffTimezone.find_timezone("America/New_York")
time = Time.new(2024, 7, 1, 12, 0, 0, in: zone)
time.utc_offset     # => -14400
time.dst?           # => true
time.strftime("%Z") # => "EDT"

# By default, requiring the gem installs Time.find_timezone if absent.
Time.at(0, in: "Asia/Tokyo")

JiffTimezone.utc
JiffTimezone.fixed(19_800) # Seconds east of UTC.
JiffTimezone.posix("EST5EDT,M3.2.0,M11.1.0")
JiffTimezone.unknown
```

`find_timezone` returns `nil` for unknown names. Invalid fixed offsets and POSIX
rules raise `ArgumentError`. Timezone objects are frozen; ordinary `new` and
`allocate` are disabled. `iana_name` returns `nil` when a zone has no IANA name.
`inspect` shows the class, timezone label, and portable representation.

Local times in DST gaps and repeated local times raise `ArgumentError`.
Construct from an instant to select either occurrence of an overlap:

```ruby
Time.at(Time.utc(2024, 11, 3, 5, 30).to_i, in: "America/New_York") # EDT
Time.at(Time.utc(2024, 11, 3, 6, 30).to_i, in: "America/New_York") # EST
```

## Initialization and Marshal

Requiring the gem initializes `JiffTimezone`. By default, it also defines
`Time.find_timezone` if absent. Existing lookup methods, including private ones,
are preserved. Repeated `require` calls reuse the loaded extension. An existing
`JiffTimezone` class is reused when it inherits from the same Magnus copy's
timezone class; its public methods are neither checked nor replaced.

To skip automatic `Time.find_timezone` registration, set
`JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION` to `0` or `false` before requiring
the gem:

```ruby
ENV["JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION"] = "false"
require "jiff_magnus"

zone = JiffTimezone.find_timezone("Asia/Tokyo")
Time.at(0, in: zone)
```

To explicitly install or replace name lookup with Jiff, even with automatic
registration disabled:

```ruby
JiffTimezone.register
Time.at(0, in: "Asia/Tokyo")
```

Registration raises `LoadError` before changing the resolver if a prepended
`singleton_method_added` hook prevents tracking the installation. Failed
registration restores the previous method and visibility while preserving
changes made by application hooks.

If `Object::JiffTimezone` already exists and does not inherit from this build's
Magnus timezone class, requiring the gem raises `LoadError`.

Require the gem before loading marshalled named-zone times. Native fixed-offset
times need no resolver. POSIX, unknown, and explicitly wrapped fixed-offset
zones have no restorable IANA name; dumping times with those objects raises
`TypeError`.

Magnus owns Rust conversions, timezone storage, and native interoperability.
The companion owns public constructors, lookup, and initialization.

## Build and test from source

For development, use Ruby 4.0 from [.ruby-version](.ruby-version), Rust 1.85 or
later, a C compiler, and libclang. From this directory, run:

```sh
bundle install
bundle exec rake
bundle exec rake build
```

The checkout builds against the current Magnus source through `path = ".."`.

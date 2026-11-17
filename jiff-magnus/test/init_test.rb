# frozen_string_literal: true

require_relative "test_helper"

class InitTest < Minitest::Test
  def test_auto_time_registration_can_be_disabled
    [
      nil,
      "1",
      "true",
      "0",
      "false",
      "FALSE"
    ].each do |setting|
      enabled = !%w[
        0
        false
        FALSE
      ].include?(setting)
      code = <<~RUBY
        require "jiff_magnus"
        abort "Unexpected automatic lookup" unless Time.respond_to?(:find_timezone, true) == #{enabled}
        zone = JiffTimezone.find_timezone("Asia/Tokyo")
        abort "Explicit timezone failed" unless Time.at(0, in: zone).utc_offset == 32400
        ENV["JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION"] = "1"
        require "jiff_magnus"
        abort "Repeated require changed lookup" unless Time.respond_to?(:find_timezone, true) == #{enabled}
        ENV["JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION"] = #{setting.inspect}
        JiffTimezone.register
        abort "Explicit registration failed" unless Time.at(0, in: "Asia/Tokyo").utc_offset == 32400
      RUBY
      output, status = Open3.capture2e(
        { "JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION" => setting },
        RbConfig.ruby, "-e", code
      )
      assert_predicate(status, :success?, "setting=#{setting.inspect}: #{output}")
    end
  end

  def test_auto_registration_optout_leaves_existing_lookup_untouched
    %w[0 false].each do |setting|
      code = <<~RUBY
        def Time.find_timezone(name)
          [:existing, name]
        end
        original = Time.method(:find_timezone)
        require "jiff_magnus"
        abort "Existing lookup changed" unless Time.method(:find_timezone) == original
        abort "Existing lookup failed" unless Time.find_timezone("UTC") == [:existing, "UTC"]
        abort "Constructors unavailable" unless JiffTimezone.utc.iana_name == "UTC"
        JiffTimezone.register
        abort "Explicit replacement failed" unless Time.find_timezone("UTC").iana_name == "UTC"
      RUBY
      output, status = Open3.capture2e(
        { "JIFF_MAGNUS_ENABLE_AUTO_TIME_REGISTRATION" => setting },
        RbConfig.ruby, "-e", code
      )
      assert_predicate(status, :success?, "setting=#{setting.inspect}: #{output}")
    end
  end

  def test_registration_explicitly_replaces_an_existing_lookup
    code = <<~RUBY
      def Time.find_timezone(name)
        [:foreign, name]
      end
      Time.singleton_class.send(:private, :find_timezone)
      require "jiff_magnus"
      abort "Existing lookup was replaced" unless Time.send(:find_timezone, "UTC") == [:foreign, "UTC"]
      abort "Constructors are unavailable" unless JiffTimezone.utc.iana_name == "UTC"
      abort "Private lookup changed visibility" if Time.respond_to?(:find_timezone)

      JiffTimezone.register
      abort "Registration did not install public lookup" unless Time.respond_to?(:find_timezone)
      abort "Registered lookup failed" unless Time.at(0, in: "Asia/Tokyo").utc_offset == 32400

      def Time.find_timezone(name)
        :replacement
      end
      JiffTimezone.register
      JiffTimezone.register
      abort "Repeated registration failed" unless Time.find_timezone("UTC").iana_name == "UTC"
    RUBY
    output, status = Open3.capture2e(RbConfig.ruby, "-e", code)
    assert_predicate(status, :success?, output)
  end
end

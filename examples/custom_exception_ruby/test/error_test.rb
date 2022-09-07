# frozen_string_literal: true

require "test/unit"
require_relative "../lib/ahriman"

class ErrorTest < Test::Unit::TestCase

  def test_error?
    assert_raise(Ahriman::RubricError) { Ahriman::cast_rubric }
  end

end

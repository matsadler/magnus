# frozen_string_literal: true

require "test/unit"
require_relative "../lib/temperature"

class TemperatureTest < Test::Unit::TestCase

  def test_new
    assert { Temperature.new(kelvin: 292.65).to_kelvin == 292.65 }
    assert { Temperature.new(celsius: 19.5).to_celsius == 19.5 }
    assert { Temperature.new(fahrenheit: 67.1).to_fahrenheit == 67.1 }
  end

  def test_to_kelvin
    temp = Temperature.new(kelvin: 292.65)
    assert { Temperature.new(kelvin: 292.65).to_kelvin == 292.65 }
    assert { Temperature.new(celsius: 19.5).to_kelvin == 292.65 }
    assert { Temperature.new(fahrenheit: 67.1).to_kelvin == 292.65 }
  end

  def test_to_celsius
    temp = Temperature.new(kelvin: 292.65)
    assert { Temperature.new(kelvin: 292.65).to_celsius == 19.5 }
    assert { Temperature.new(celsius: 19.5).to_celsius == 19.5 }
    assert { Temperature.new(fahrenheit: 67.1).to_celsius == 19.5 }
  end

  def test_to_fahrenheit
    temp = Temperature.new(kelvin: 292.65)
    assert { Temperature.new(kelvin: 292.65).to_fahrenheit == 67.1 }
    assert { Temperature.new(celsius: 19.5).to_fahrenheit == 67.1 }
    assert { Temperature.new(fahrenheit: 67.1).to_fahrenheit == 67.1 }
  end

  def test_dup
    temp = Temperature.new(celsius: 19.5)
    def temp.singlton_method_example
    end
    copy = temp.dup

    assert { temp.object_id != copy.object_id }
    assert { temp == copy }
    assert { !copy.frozen? }
    assert { !copy.respond_to?(:singlton_method_example)}

    temp2 = Temperature.new(celsius: 19.5)
    temp2.freeze
    copy2 = temp2.dup
    assert { !copy2.frozen? }
  end

  def test_clone
    temp = Temperature.new(celsius: 19.5)
    def temp.singlton_method_example
    end
    copy = temp.clone

    assert { temp.object_id != copy.object_id }
    assert { temp == copy }
    assert { !copy.frozen? }
    assert { copy.respond_to?(:singlton_method_example)}

    temp2 = Temperature.new(celsius: 19.5)
    temp2.freeze
    copy2 = temp2.clone
    assert { copy2.frozen? }

    temp3 = Temperature.new(celsius: 19.5)
    copy3 = temp3.clone(freeze: true)
    assert { copy3.frozen? }

    temp4 = Temperature.new(celsius: 19.5)
    temp4.freeze
    copy4 = temp4.clone(freeze: false)
    assert { !copy4.frozen? }
  end

  def test_hash
    freezing = Temperature.new(celsius: 0)
    boiling = Temperature.new(celsius: 100)

    hash = {freezing => :cold, boiling => :hot}

    assert { hash[Temperature.new(fahrenheit: 32)] == :cold }
    assert { hash[Temperature.new(fahrenheit: 212)] == :hot }
  end

  def test_sort
    temps = [Temperature.new(celsius: 25), Temperature::new(fahrenheit: 80), Temperature::new(kelvin: 273.15)]

    assert { temps.sort == [Temperature::new(kelvin: 273.15), Temperature.new(celsius: 25), Temperature::new(fahrenheit: 80)] }
    assert { Temperature.new(celsius: 40) > Temperature.new(fahrenheit: 90)}
    assert { Temperature.new(fahrenheit: 32) < Temperature.new(celsius: 1)}
    assert { Temperature.new(celsius: -40) == Temperature.new(fahrenheit: -40 )}
  end

  def test_inspect
    assert { Temperature.new(celsius: 19.5).inspect == "Temperature { microkelvin: 292650000 }" }
  end

  def test_to_s
    assert { Temperature.new(celsius: 19.5).to_s == "19.5°C" }
  end
end

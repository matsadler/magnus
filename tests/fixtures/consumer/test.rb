# frozen_string_literal: true

require ARGV.fetch(0)

["", "hello", "é" * 100].each do |string|
  raise "string length mismatch" unless MagnusConsumer.string_length(string) == string.bytesize
  raise "string data mismatch" unless MagnusConsumer.string_copy(string) == string
end

[[], [1, 2], (1..100).to_a].each do |array|
  raise "array length mismatch" unless MagnusConsumer.array_length(array) == array.length
  raise "array data mismatch" unless MagnusConsumer.array_sum(array) == array.sum
end

number = MagnusConsumer::Number.new(42)
raise "typed-data mismatch" unless number.value == 42
GC.start
GC.compact if GC.respond_to?(:compact)
raise "typed-data mismatch after GC" unless number.value == 42
puts "Strings, arrays, and typed data passed"

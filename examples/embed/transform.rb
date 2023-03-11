class Transform
  def self.run
    source = WordSource.new
    sink = WordSink.new

    source.each do |word|
      sink << word.reverse
    end
  end
end
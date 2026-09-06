# typed: true

class Collector
  #: Array[[String, Integer]]
  attr_reader :items

  #: () -> void
  def initialize
    @items = [] #: Array[[String, Integer]]
  end

  #: (String) -> void
  def add(value)
    @items << [value, 1]
  end
end

Collector.new.add("value")

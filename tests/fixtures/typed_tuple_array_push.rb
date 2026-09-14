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

collector = Collector.new
collector.add("value")
T.reveal_type(collector.items) # note: T::Array[[String, Integer]]

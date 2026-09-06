# typed: true

class Collector
  def initialize
    @items = [] #: Array[String]
  end

  def reset
    @items = []
    @items << "ready"
  end

  def items
    @items
  end
end

collector = Collector.new
collector.reset
T.reveal_type(collector.items) # note: T::Array[String]

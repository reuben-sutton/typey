# typed: true

class BaseCollector
  def initialize
    @items = [] #: Array[String]
  end
end

class ChildCollector < BaseCollector
  def items
    @items << "ready"
    @items
  end
end

T.reveal_type(ChildCollector.new.items) # note: T::Array[String]

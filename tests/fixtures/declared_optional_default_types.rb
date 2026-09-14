# typed: true

class Collector
  #: (?items: Array[String]) -> void
  def initialize(items: [])
    @items = items
  end

  #: -> bool
  def ruby_file?
    @items.any? { |item| item.end_with?(".rb") }
  end
end

T.reveal_type(Collector.new.ruby_file?) # note: T::Boolean

# typed: true

class InitializedWithoutConstruction
  def initialize
    @items = []
  end

  def each_item
    T.reveal_type(@items) # note: Revealed type: `T::Array[T.untyped]`
    @items.each { |item| T.reveal_type(item) } # note: Revealed type: `T.untyped`
  end
end

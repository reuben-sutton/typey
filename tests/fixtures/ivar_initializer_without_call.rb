# typed: true

class InitializedWithoutConstruction
  def initialize
    @items = []
  end

  def each_item
    @items.each { |item| item }
  end
end

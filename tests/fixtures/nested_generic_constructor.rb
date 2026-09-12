# typed: true

module Spoom
  #: [E < Object]
  class Poset
    #: [E < Object]
    class Element
      #: (E value) -> void
      def initialize(value)
        @value = value #: E
      end
    end

    #: -> void
    def initialize
      @elements = {} #: Hash[E, Element[E]]
    end

    #: (E value) -> Element[E]
    def add_element(value)
      element = @elements[value]
      return element if element

      @elements[value] = Element.new(value) #: Element[E]
    end
  end
end

T.reveal_type(Spoom::Poset[String].new.add_element("value")) # note: Revealed type: `Spoom::Poset::Element[String]`

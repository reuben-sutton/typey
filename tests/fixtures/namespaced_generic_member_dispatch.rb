# typed: true

module Spoom
  #: [E < Object]
  class Poset
    #: (E value) -> E
    def [](value)
      value
    end
  end
end

poset = Spoom::Poset.new #: Spoom::Poset[String]
T.reveal_type(poset)
value = poset["value"]
T.reveal_type(value)

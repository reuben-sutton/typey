module Namespace
  class Thing
    VALUE = "nested"

    def self.value
      VALUE
    end
  end
end

T.reveal_type(Namespace::Thing.value) # note: String

extend T::Sig

sig { params(value: Module).void }
def accepts_module(value)
end

accepts_module(Namespace::Thing)

module Outer
  class Symbol
  end

  class Registry
    #: -> Symbol
    def build
      Symbol.new
    end
  end
end

T.reveal_type(Outer::Registry.new.build) # note: Outer::Symbol

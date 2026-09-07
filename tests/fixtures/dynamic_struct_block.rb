# typed: true

module Example
  Parameter = Struct.new(:escaper) do
    def escape(value)
      T.reveal_type(escaper) # note: Revealed type: `T.proc.params(T.untyped).returns(String)`
      T.reveal_type(escaper.call(value)) # note: Revealed type: `String`
      escaper.call(value)
    end
  end
end

parameter = Example::Parameter.new(->(value) { value.to_s })
T.reveal_type(parameter.escaper) # note: Revealed type: `T.proc.params(T.untyped).returns(String)`
parameter.escape("value")

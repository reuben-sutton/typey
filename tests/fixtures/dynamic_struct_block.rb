# typed: true

module Example
  Parameter = Struct.new(:escaper) do
    def escape(value)
      T.reveal_type(escaper)
      T.reveal_type(escaper.call(value))
      escaper.call(value)
    end
  end
end

parameter = Example::Parameter.new(->(value) { value.to_s })
T.reveal_type(parameter.escaper)
parameter.escape("value")

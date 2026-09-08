# typed: true

class PositionalHashArgument
  extend T::Sig

  sig { params(value: T::Hash[String, Integer]).returns(T::Hash[String, Integer]) }
  def accept(value)
    value
  end
end

T.reveal_type(PositionalHashArgument.new.accept("key" => 1)) # note: T::Hash[String, Integer]

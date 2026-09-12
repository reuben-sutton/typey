# typed: true

class Set
  extend T::Sig

  sig do
    type_parameters(:U).params(ary: T.type_parameter(:U))
      .returns(T::Set[T.type_parameter(:U)])
  end
  def self.[](*ary)
    raise "stub"
  end
end

T.reveal_type(Set["one", "two"]) # note: T::Set[String]

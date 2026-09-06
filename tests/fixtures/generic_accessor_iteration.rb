# typed: true

class IndexedValues
  #: Hash[String, Array[Integer]]
  attr_reader :values

  def initialize
    @values = {"numbers" => [1]} #: Hash[String, Array[Integer]]
  end
end

class SignedIndexedValues
  sig { returns(T::Hash[String, T::Array[Integer]]) }
  def values
    {"numbers" => [1]}
  end
end

IndexedValues.new.values.each do |_name, values|
  values.each do |value|
    T.reveal_type(value) # note: Integer
  end
end

SignedIndexedValues.new.values.each do |_name, values|
  values.each do |value|
    T.reveal_type(value) # note: Integer
  end
end

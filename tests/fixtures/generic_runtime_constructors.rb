# typed: true

extend T::Sig

sig { returns(T::Array[Integer]) }
def typed_array_constructor
  value = T::Array[Integer].new
  T.reveal_type(value) # note: Revealed type: `T::Array[Integer]`
  value
end

sig { returns(T::Hash[String, Integer]) }
def typed_hash_constructor
  value = T::Hash[String, Integer].new
  T.reveal_type(value) # note: Revealed type: `T::Hash[String, Integer]`
  value
end

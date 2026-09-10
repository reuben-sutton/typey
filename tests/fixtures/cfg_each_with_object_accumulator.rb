array_result = [1].each_with_object([]) do |value, output|
  output << value.to_s
end
T.reveal_type(array_result) # note: Revealed type: `T::Array[T.untyped]`

hash_result = [1].each_with_object({}) do |value, output|
  output[value.to_s] = value
end
T.reveal_type(hash_result) # note: Revealed type: `T::Hash[T.untyped, T.untyped]`

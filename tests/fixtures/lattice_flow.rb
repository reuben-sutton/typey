x = T.let(nil, T.nilable(String))

if x
  T.reveal_type(x) # note: String
else
  T.reveal_type(x) # note: NilClass
end

values = [1, 2.0]
T.reveal_type(values) # note: T::Array[T.any(Float, Integer)]

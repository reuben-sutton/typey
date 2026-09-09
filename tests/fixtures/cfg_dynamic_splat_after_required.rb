# typed: true

sig { params(first: Integer, values: T.untyped).void }
def accepts_rest_after_required(first, *values)
end

sig { returns(T::Array[Integer]) }
def dynamic_integer_values
  [1, 2]
end

accepts_rest_after_required(0, *dynamic_integer_values)

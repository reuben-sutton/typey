# typed: true

extend T::Sig

sig { params(value: T.any(Integer, String)).void }
def narrows_equal_integer(value)
  if value.equal?(0)
    T.assert_type!(value, Integer)
  else
    T.assert_type!(value, T.any(Integer, String))
  end
end

sig { params(value: T.nilable(Integer)).void }
def narrows_equal_nil(value)
  if value == nil
    T.assert_type!(value, NilClass)
  else
    T.assert_type!(value, Integer)
  end
end

sig { params(value: T.any(Integer, TrueClass)).void }
def narrows_not_equal_true(value)
  if value != true
    T.assert_type!(value, Integer)
  else
    T.assert_type!(value, TrueClass)
  end
end

sig { params(value: T.nilable(Integer)).void }
def narrows_through_negated_boolean_alias(value)
  is_nil = !value
  if is_nil
    T.assert_type!(value, NilClass)
  else
    T.assert_type!(value, Integer)
  end
end

sig { params(value: T.nilable(Integer)).void }
def narrows_through_negated_type_predicate_alias(value)
  is_not_integer = !value.is_a?(Integer)
  if is_not_integer
    T.assert_type!(value, NilClass)
  else
    T.assert_type!(value, Integer)
  end
end

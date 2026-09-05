#: (Integer, String?) -> String
def format_value(value, suffix)
  value.to_s + suffix.to_s
end

format_value("wrong", nil) # error: Expected `Integer`, but found `String`

values = [1, 2] #: T::Array[Integer]
T.reveal_type(values) # note: T::Array[Integer]

optional_value =
  nil #: Integer?
T.reveal_type(optional_value) # note: T.nilable(Integer)

nil_value = nil #: as !nil # error: Expected a non-nil value

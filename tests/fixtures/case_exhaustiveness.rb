# typed: true

extend T::Sig

sig { params(value: T.any(String, [String, String])).returns(String) }
def describe_value(value)
  case value
  when String
    value
  when Array
    value[0]
  else
    T.absurd(value)
  end
end

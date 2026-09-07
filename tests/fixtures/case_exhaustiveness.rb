# typed: true

extend T::Sig

sig { params(value: T.any(String, [String, String])).returns(T.nilable(String)) }
def describe_value(value)
  case value
  when String
    T.reveal_type(value) # note: String
    value
  when Array
    T.reveal_type(value[0]) # note: T.nilable(String)
    value[0]
  else
    T.absurd(value)
  end
end

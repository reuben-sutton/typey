# typed: true

extend T::Sig

sig { params(value: String).returns(String) }
sig { params(value: Integer).returns(Integer) }
def identity(value)
  value
end

T.reveal_type(identity("value")) # note: String
T.reveal_type(identity(1)) # note: Integer

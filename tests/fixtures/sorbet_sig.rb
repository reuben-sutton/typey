extend T::Sig

sig { params(value: Integer).returns(String) }
def to_text(value)
  T.reveal_type(value) # note: Integer
  value.to_s
end

to_text("wrong") # error: Expected `Integer`, but found `String`

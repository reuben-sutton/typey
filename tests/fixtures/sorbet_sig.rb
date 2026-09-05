sig { params(value: Integer).returns(String) }
def to_text(value)
  value.to_s
end

to_text("wrong") # error: Expected `Integer`, but found `String`

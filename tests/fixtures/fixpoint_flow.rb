# The call appears before both definitions; registration and summary rounds
# should still resolve the result through both methods.
T.reveal_type(first(1)) # note: String

def first(value)
  second(value)
end

def second(value)
  value.to_s
end

def identity(value)
  value
end

T.reveal_type(identity(1)) # note: T.any(Integer, String)
T.reveal_type(identity("text")) # note: T.any(Integer, String)

# typed: true

def uses_default(limit = 1)
  T.reveal_type(limit) # note: Integer
  limit.to_i
end

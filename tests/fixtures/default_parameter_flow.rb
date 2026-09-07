# typed: true

def uses_default(limit = 1)
  T.reveal_type(limit) # note: T.untyped
  limit.to_i
end

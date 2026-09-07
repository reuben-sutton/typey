# typed: true

def default_sentinel(value = (sentinel = true))
  if sentinel
    value
  else
    T.reveal_type(sentinel) # note: NilClass
    value
  end
end

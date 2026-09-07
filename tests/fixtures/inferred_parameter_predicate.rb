# typed: true

def choose(value)
  if value
    "truthy"
  else
    0
  end
end

T.reveal_type(choose(true)) # note: T.any(Integer, String)

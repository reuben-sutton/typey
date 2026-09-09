fallback = raise "boom" rescue "fallback"
T.reveal_type(fallback) # note: Revealed type: String

def value
  fallback = raise "boom" rescue "fallback"
  T.reveal_type(fallback) # note: Revealed type: String
end

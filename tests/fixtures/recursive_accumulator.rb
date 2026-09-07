# typed: true

def recursive_append(value, seed)
  if value == 0
    seed << "x"
  else
    recursive_append(value - 1, seed) << "y"
  end
end

T.reveal_type(recursive_append(1, "")) # note: Revealed type: `String`

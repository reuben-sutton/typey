def current_match
  T.reveal_type($&) # note: Revealed type: `T.untyped`
end

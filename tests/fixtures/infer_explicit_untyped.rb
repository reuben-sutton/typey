# typed: true

# An explicit gradual signature is normally an intentional boundary.  The
# opt-in checker mode may replace only its untyped slots with evidence.
#: (untyped) -> untyped
def explicit_untyped_add(value)
  value + 1
end

explicit_untyped_add(1)
T.reveal_type(explicit_untyped_add(1)) # note: Revealed type: `T.untyped`

#: () -> untyped
def explicit_untyped_literal
  1
end

T.reveal_type(explicit_untyped_literal) # note: Revealed type: `T.untyped`

#: (untyped) -> String
def explicit_untyped_fixed_return(value)
  value.to_s
end

T.reveal_type(explicit_untyped_fixed_return(1)) # note: Revealed type: `String`

#: (untyped) -> untyped
def explicit_untyped_missing_method(value)
  value.not_a_method
end

explicit_untyped_missing_method("text")

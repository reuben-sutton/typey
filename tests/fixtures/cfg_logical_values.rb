# typed: true

# The RHS is evaluated only on the path selected by the LHS truthiness.
maybe = T.let(nil, T.nilable(String))
T.reveal_type(maybe && maybe.upcase) # note: T.nilable(String)
T.reveal_type(maybe || "fallback") # note: String

#: (String?) -> String?
def logical_value(value)
  value && value.to_s
end

T.reveal_type(logical_value(nil)) # note: String

# Predicate facts from both sides of a logical condition survive the join when
# the non-matching branch cannot complete normally.
#: (String?) -> String
def logical_guard(value)
  return "fallback" unless value && value.start_with?("prefix")

  value.upcase
end

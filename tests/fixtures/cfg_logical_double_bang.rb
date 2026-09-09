# typed: true

# A double negation is still a refinement of the original operand.
#: (String?) -> String
def double_bang_guard(value)
  return "fallback" unless !!value && value.start_with?("prefix")

  value.upcase
end

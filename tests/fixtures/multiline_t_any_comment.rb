# typed: true

sig do
  params(
    value: T.any(
      String,
      Integer, # Numeric values are also accepted.
      Float,
    )
  ).void
end
def accepts_string_or_number(value)
  T.reveal_type(value) # note: T.any(Float, Integer, String)
end

T.reveal_type(accepts_string_or_number("version")) # note: NilClass

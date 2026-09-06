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
def accepts_string_or_number(value); end

accepts_string_or_number("version")

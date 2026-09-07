# typed: true

[
  ["one", "ONE"],
  ["two", "TWO"],
].each do |value, label|
  T.reveal_type(value) # note: String
  T.reveal_type(label) # note: String
  value.start_with?("o")
end

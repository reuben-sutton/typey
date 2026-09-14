# typed: true

strings = T.let(["foo"], T::Array[String])
T.reveal_type(strings) # note: Revealed type: T::Array[String]
strings.any? { |value| T.reveal_type(value.end_with?("o")) } # note: Revealed type: T::Boolean

entries = T.let({"foo" => 1}, T::Hash[String, Integer])
entries.all? do |key, value|
  T.reveal_type(key) # note: Revealed type: String
  T.reveal_type(value) # note: Revealed type: Integer
  key.start_with?("f") && value > 0
end

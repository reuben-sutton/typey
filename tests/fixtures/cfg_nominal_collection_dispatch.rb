# typed: true

numbers = T.let([1, 2, 3], T::Array[Integer])
T.reveal_type(numbers.sort_by { |value| -value }) # note: T::Array[Integer]
T.reveal_type(numbers.find { |value| value == 2 }) # note: T.nilable(Integer)
T.reveal_type(numbers.each_with_index { |_value, index| index }) # note: T::Array[Integer]

entries = T.let({"a" => 1}, T::Hash[String, Integer])
T.reveal_type(entries.sort_by { |_key, value| value }) # note: T::Array[[String, Integer]]
T.reveal_type(entries.any? { |key, _value| key == "a" }) # note: T::Boolean

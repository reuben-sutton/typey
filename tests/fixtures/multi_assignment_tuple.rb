# typed: true

first, rest = "first", ["second"]

T.assert_type!(first, String)
T.assert_type!(rest, T::Array[String])
first.upcase
rest.each { |value| value.upcase }

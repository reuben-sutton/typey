# typed: true

values = [1, 2, 3]
T.reveal_type(values.slice(0)) # note: T.nilable(Integer)

counts = {"one" => 1}
counts["two"] = 2
T.reveal_type(counts.to_json) # note: String

NAMES = ["one"] #: Array[String]
T.reveal_type(NAMES.include?("one")) # note: T::Boolean

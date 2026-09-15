# typed: true

T.reveal_type(Set.new([1, 2, 3])) # note: Set[Integer]
T.reveal_type(Set.new(["one", "two"])) # note: Set[String]

# typed: true

first, second, third = *ExternalNode.new
T.reveal_type(first)
T.reveal_type(second)
T.reveal_type(third)

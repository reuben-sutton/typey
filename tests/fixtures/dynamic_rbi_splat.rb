# typed: true

first, second, third = *ExternalNode.new
T.reveal_type(first) # note: Revealed type: `T.untyped`
T.reveal_type(second) # note: Revealed type: `T.untyped`
T.reveal_type(third) # note: Revealed type: `T.untyped`

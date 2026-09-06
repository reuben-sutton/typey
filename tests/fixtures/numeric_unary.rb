# typed: true

T.reveal_type(-Float::INFINITY) # note: Float
T.reveal_type(+Float::INFINITY) # note: Float
T.reveal_type(-1) # note: Integer

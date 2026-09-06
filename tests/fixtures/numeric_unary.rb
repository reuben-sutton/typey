# typed: true

float = T.let(T.unsafe(nil), Float)
T.reveal_type(-float) # note: Float
T.reveal_type(+float) # note: Float
T.reveal_type(-1) # note: Integer

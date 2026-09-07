# typed: true

T.reveal_type([1, 0].max) # note: Integer
T.reveal_type([1, 0].min) # note: Integer
T.reveal_type([].max) # note: T.untyped

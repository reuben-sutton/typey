T.reveal_type([1].map { it + 1 }) # note: Revealed type: `T::Array[Integer]`
T.reveal_type([1].map { _1 + 1 }) # note: Revealed type: `T::Array[Integer]`
T.reveal_type([1].each_with_index { _2 + 1 }) # note: Revealed type: `T::Array[Integer]`

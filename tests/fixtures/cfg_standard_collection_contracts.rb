values = [1, 2]
T.reveal_type(values.zip(["a"])) # note: Revealed type: `T::Array[[Integer, T.nilable(String)]]`
T.reveal_type([["a"]].flatten) # note: Revealed type: `T::Array[T.untyped]`
T.reveal_type(values.product(["a"])) # note: Revealed type: `T::Array[T.untyped]`
T.reveal_type(values.sum) # note: Revealed type: `Integer`
T.reveal_type(values.combination(1)) # note: Revealed type: `T::Enumerator[T::Array[Integer]]`
T.reveal_type(values.select! { |value| value.even? }) # note: Revealed type: `T.nilable(T::Array[Integer])`
T.reveal_type(values.fill(0)) # note: Revealed type: `T::Array[Integer]`
T.reveal_type(values.replace([3])) # note: Revealed type: `T::Array[Integer]`
T.reveal_type(values.uniq!) # note: Revealed type: `T.nilable(T::Array[Integer])`
T.reveal_type(values.bsearch { |value| value > 0 }) # note: Revealed type: `T.nilable(Integer)`
T.reveal_type("text".encode) # note: Revealed type: `String`
T.reveal_type(1.clamp(0, 2)) # note: Revealed type: `T.untyped`
T.reveal_type(1.downto(0)) # note: Revealed type: `T::Enumerator[Integer]`

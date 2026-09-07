# typed: true

extend T::Sig

sig { returns([T::Array[String], T::Array[String]]) }
def typed_pair
  [[], []]
end

sig { returns(T::Boolean) }
def choose_pair
  true
end

first, second = choose_pair ? typed_pair : [[], []]
T.reveal_type(first) # note: Revealed type: `T::Array[String]`
T.reveal_type(second) # note: Revealed type: `T::Array[String]`

# typed: true

T.reveal_type(T.proc.params(value: String).returns(Integer)) # note: Revealed type: `T::Types::Proc`
T.reveal_type(T.nilable(T.proc.params(value: String).void)) # note: Revealed type: `T::Types::Union`

def cast_callback(value)
  T.cast(value, T.nilable(T.proc.params(value: String).returns(Integer)))
end

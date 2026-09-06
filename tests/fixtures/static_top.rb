# typed: true

extend T::Sig

sig { params(value: T.anything).void }
def static_top(value)
  T.reveal_type(value) # note: Revealed type: `T.anything`
  value.export # error: Method `export` does not exist on `T.anything`
end

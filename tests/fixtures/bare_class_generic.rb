# typed: true

extend T::Sig

sig { params(klass: Class).void }
def bare_class(klass)
  T.reveal_type(klass) # note: Revealed type: `Class[T.anything]`
  instance = klass.new
  T.reveal_type(instance) # note: Revealed type: `T.anything`
  instance.foo # error: Method `foo` does not exist on `T.anything`
end

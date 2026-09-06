# typed: true

class First
end

class Second
end

extend T::Sig
sig { params(value: First).void }
def nominal_predicate(value)
  if value.is_a?(Second)
    value # error: This code is unreachable
  end
  T.reveal_type(value) # note: Revealed type: `First`
end

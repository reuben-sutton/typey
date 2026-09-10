# typed: true

class GenericHashConstructor
  def self.run
    T.reveal_type(Hash[[[1, 2]]]) # note: Revealed type: `T::Hash[Integer, Integer]`
  end
end

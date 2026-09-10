# typed: true

class GenericHashConstructor
  def self.run
    T.reveal_type(Hash[[[1, 2]]])
  end
end

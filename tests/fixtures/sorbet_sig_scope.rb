# typed: true

class ValidClassSigScope
  extend T::Sig

  sig do
    returns(Integer)
  end
  def value
    1
  end
end

class InvalidSingletonSigScope
  extend T::Sig

  class << self
    sig do # error: Method `sig` does not exist
      returns(Integer) # error: Method `returns` does not exist
    end
    def value
      1
    end
  end
end

class ValidSingletonSigScope
  class << self
    extend T::Sig

    sig do
      returns(Integer)
    end
    def value
      1
    end
  end
end

sig do # error: Method `sig` does not exist
  returns(Integer) # error: Method `returns` does not exist
end
def invalid_top_level_sig
  1
end

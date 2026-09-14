# typed: true

class StringVariant
  extend T::Sig

  sig { returns(String) }
  def value
    "string"
  end
end

class IntegerVariant
  extend T::Sig

  sig { returns(Integer) }
  def value
    1
  end
end

union = T.let(T.unsafe(nil), T.any(StringVariant, IntegerVariant))
T.reveal_type(union.value) # note: T.any(Integer, String)

class NameProvider
  extend T::Sig

  sig { returns(String) }
  def name
    "name"
  end
end

class LocationProvider
  extend T::Sig

  sig { returns(Integer) }
  def location
    1
  end
end

intersection = T.let(T.unsafe(nil), T.all(NameProvider, LocationProvider))
T.reveal_type(intersection.name) # note: String
T.reveal_type(intersection.location) # note: Integer

# typed: true

class LeftCollection
  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def any?(&block)
    true
  end

  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def all?(&block)
    true
  end

  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def none?(&block)
    true
  end
end

class RightCollection
  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def any?(&block)
    true
  end

  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def all?(&block)
    true
  end

  #: () ?{ (Integer) -> T::Boolean } -> T::Boolean
  def none?(&block)
    true
  end
end

#: (LeftCollection | RightCollection) -> T::Boolean
def check_predicates(values)
  values.any? { |value| value > 0 }
  values.all? { |value| value > 0 }
  values.none? { |value| value < 0 }
end

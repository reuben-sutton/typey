# typed: true

#: (T::Enumerable[String]) -> void
def consume(values)
  values.each { |value| value.length }
end

module Enumerable
end

class Set
  include Enumerable
end

values = T.let(Set.new, T::Set[String])
consume(values)

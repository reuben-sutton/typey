# typed: true

#: (T::Enumerable[String]) -> void
def consume(values)
  values.each { |value| value.length }
end

values = T.let(Set.new, T::Set[String])
consume(values)

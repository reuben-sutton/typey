# typed: true

class MultiAssignedState
  #: (Integer, T::Hash[Symbol, Integer]) -> void
  def initialize(value, parts)
    @value, @parts = value, parts
  end

  #: -> Integer
  def seconds
    @parts.fetch(:seconds, 0)
  end
end

T.reveal_type(MultiAssignedState.new(1, {seconds: 2}).seconds) # note: Integer

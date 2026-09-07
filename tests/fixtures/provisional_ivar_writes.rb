# typed: true

class ProvisionalIvarWrites
  def initialize
    @value = "stable"
  end

  # The first pass sees `value` provisionally as T.untyped. The later write is
  # concrete; that sequence must not make the shared ivar oscillate forever.
  def update(value)
    @value = value
    @value = "stable"
  end

  def value
    @value
  end
end

object = ProvisionalIvarWrites.new
object.update("updated")
T.reveal_type(object.value) # note: String

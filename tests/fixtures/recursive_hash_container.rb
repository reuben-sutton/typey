# typed: true

class InheritableOptions < Hash
  def initialize(parent)
    @parent = parent
  end

  def to_h
    @parent.to_h.merge(self)
  end

  def keys
    @parent.keys | super
  end
end

T.reveal_type(InheritableOptions.new(InheritableOptions.new({})).to_h) # note: T::Hash[T.untyped, T.untyped]

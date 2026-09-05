module Printable
  def printable(value)
    value.to_s
  end
end

class Included
  include Printable
end

module Preferred
  def label(value)
    :preferred
  end
end

class Prepared
  prepend Preferred

  def label(value)
    value.to_s
  end
end

class Parent
  def render(value)
    value.to_s
  end
end

class Child < Parent
  def render(value)
    super(value)
  end
end

class Aliased
  def original(value)
    value.to_s
  end

  alias renamed original
  alias_method :renamed_again, :original
end

T.reveal_type(Included.new.printable(1)) # note: String
T.reveal_type(Prepared.new.label(1)) # note: Symbol
T.reveal_type(Child.new.render(1)) # note: String
T.reveal_type(Aliased.new.renamed(1)) # note: String
T.reveal_type(Aliased.new.renamed_again(1)) # note: String

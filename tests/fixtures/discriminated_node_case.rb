class Node
  #: () -> Symbol
  def type
    raise "abstract"
  end
end

class Cat < Node
  attr_reader :right

  #: () -> Symbol
  def type
    :CAT
  end
end

class Or < Node
  attr_reader :children

  #: () -> Symbol
  def type
    :OR
  end
end

#: (Node) -> Object
def render(node)
  case node.type
  when :CAT
    T.reveal_type(node) # note: Revealed type: `Cat`
    node.right
  when :OR
    T.reveal_type(node) # note: Revealed type: `Or`
    node.children
  end
end

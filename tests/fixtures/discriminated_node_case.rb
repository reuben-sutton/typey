class Node
  def type
    raise "abstract"
  end
end

class Cat < Node
  attr_reader :right

  def type
    :CAT
  end
end

class Or < Node
  attr_reader :children

  def type
    :OR
  end
end

def render(node)
  case node.type
  when :CAT
    node.right
  when :OR
    node.children
  end
end

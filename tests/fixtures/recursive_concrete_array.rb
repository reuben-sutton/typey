# typed: true

class RecursiveConcreteArrayNode
  #: (String name, Array[RecursiveConcreteArrayNode] children) -> void
  def initialize(name, children)
    @name = name
    @children = children
  end

  #: String
  attr_reader :name

  #: Array[RecursiveConcreteArrayNode]
  attr_reader :children
end

def recursive_names(node)
  current = [node.name]
  descendants = node.children.flat_map { |child| recursive_names(child) }
  current + descendants
end

T.reveal_type(
  recursive_names( # note: Revealed type: `T::Array[String]`
    RecursiveConcreteArrayNode.new(
      "root",
      [RecursiveConcreteArrayNode.new("leaf", [])]
    )
  )
)

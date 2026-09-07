# typed: true

class AST::Node
  def type
    :node
  end
end

class Parser::AST::Node < AST::Node
end

node = T.cast(T.unsafe(nil), Parser::AST::Node)
T.reveal_type(node.type)

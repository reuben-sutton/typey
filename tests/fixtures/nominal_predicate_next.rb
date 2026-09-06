# typed: true

class AstNode
end

class Comment
end

extend T::Sig
sig { params(nodes: T::Array[AstNode]).void }
def skip_comments(nodes)
  nodes.each do |node|
    next if node.is_a?(Comment) # error: This code is unreachable

    node
  end
end

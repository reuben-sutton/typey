# typed: true

class InferenceNode
end

class InferenceParserNode < InferenceNode
end

module InferenceParserHelper
  def self.parse
    InferenceParserNode.new
  end
end

def parse_inference_node
  T.must(InferenceParserHelper.parse)
end

class InferenceNodeCollection
  #: -> Array[InferenceParserNode]
  def entries
    [InferenceParserNode.new]
  end
end

def parse_inference_nodes
  InferenceNodeCollection.new
end

#: (Array[InferenceNode]) -> void
def consume_inference_nodes(nodes)
end

def check_inference_node
  node = parse_inference_nodes.entries[1]
  grandparent = parse_inference_node
  consume_inference_nodes([node, grandparent]) # error: Expected `T::Array[InferenceNode]`, but found `T::Array[T.nilable(InferenceParserNode)]`
end

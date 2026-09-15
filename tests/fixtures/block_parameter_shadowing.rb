# typed: true

class BlockParameterShadowing
  #: (String) -> void
  def visit(node)
    [1].each do |node|
      T.reveal_type(node) # note: Integer
    end

    T.reveal_type(node) # note: String
  end
end

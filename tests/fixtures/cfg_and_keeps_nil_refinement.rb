# typed: true

class CfgAndRefinement
  #: (CfgAndRefinement? node) -> bool
  def self.dynamic?(node)
    !!node && constant?(node) && constant_name(node) == "value"
  end

  #: (CfgAndRefinement node) -> bool
  def self.constant?(node)
    true
  end

  #: (CfgAndRefinement node) -> String
  def self.constant_name(node)
    "value"
  end
end

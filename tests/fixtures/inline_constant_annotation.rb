# typed: true

module CfgInlineConstantNamespace
  HIGHLIGHT = CfgInlineConstantNamespace::Color::BLUE #: CfgInlineConstantNamespace::Color

  def self.highlight(value)
    value.to_s
  end

  class Color
    BLUE = new #: CfgInlineConstantNamespace::Color
  end
end

T.reveal_type(CfgInlineConstantNamespace::HIGHLIGHT) # note: CfgInlineConstantNamespace::Color
CfgInlineConstantNamespace.highlight(CfgInlineConstantNamespace::HIGHLIGHT)

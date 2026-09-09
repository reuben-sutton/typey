# typed: true

class CfgTapBlock
end

value = CfgTapBlock.new.tap do |item|
  T.reveal_type(item) # note: CfgTapBlock
end
T.reveal_type(value) # note: CfgTapBlock


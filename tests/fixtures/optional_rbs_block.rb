# typed: true

module OptionalRbsBlock
  #: (String value) ?{ (String value) -> void } -> String
  def self.call(value, &block)
    return value unless block

    block.call(value)
    value
  end
end

T.reveal_type(OptionalRbsBlock.call("value")) # note: String
OptionalRbsBlock.call(1) # error: Expected `String`, but found `Integer`

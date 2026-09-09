# typed: true

# Ruby 3 keyword/hash shorthand must retain the local's concrete type in HIR.
value = "text"
options = { value: }
T.reveal_type(options[:value]) # note: String

class CfgKeywordShorthand
  #: (value: String) -> String
  def self.consume(value:)
    value
  end
end

T.reveal_type(CfgKeywordShorthand.consume(value:)) # note: String

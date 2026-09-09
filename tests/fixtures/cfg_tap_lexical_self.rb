# typed: true

class CfgTapLexicalSelf
  def self.helper
    "helper"
  end

  def self.run
    "value".tap { |value| helper }
  end
end

T.reveal_type(CfgTapLexicalSelf.run) # note: String

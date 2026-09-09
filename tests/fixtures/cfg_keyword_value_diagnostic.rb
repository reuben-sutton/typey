# typed: true

class KeywordDiagnostic
  #: (value: String) -> void
  def self.consume(value:); end
end

KeywordDiagnostic.consume(value: 1) # error: Expected `String`, but found `Integer`

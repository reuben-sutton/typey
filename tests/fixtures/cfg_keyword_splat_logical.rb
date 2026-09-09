# typed: true

class CfgKeywordSplatLogical
  def self.consume(**options)
    options[:value]
  end
end

options = {value: 1}
CfgKeywordSplatLogical.consume(**(options || {}))

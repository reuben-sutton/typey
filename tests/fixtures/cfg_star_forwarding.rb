# typed: true

class CfgStarForwarding
  def self.target(*values)
    values.first
  end

  def self.wrapper(*)
    target(*)
  end

  def self.keyword_target(**options)
    options[:value]
  end

  def self.keyword_wrapper(**)
    keyword_target(**)
  end
end

CfgStarForwarding.wrapper(1)
CfgStarForwarding.keyword_wrapper(value: 1)

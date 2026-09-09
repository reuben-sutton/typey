# typed: true

class CfgStarForwarding
  def self.target(*values)
    values.first
  end

  def self.wrapper(*)
    target(*)
  end
end

CfgStarForwarding.wrapper(1)

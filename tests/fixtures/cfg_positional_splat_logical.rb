# typed: true

class CfgPositionalSplatLogical
  def self.consume(*values)
    values.first
  end
end

values = [1]
CfgPositionalSplatLogical.consume(*(values || []))

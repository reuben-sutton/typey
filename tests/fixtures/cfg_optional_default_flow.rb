# typed: true
# conformance: cfg

class CfgOptionalDefaultFlow < Hash
  def initialize(parent = nil)
    @parent = parent
    if @parent.kind_of?(CfgOptionalDefaultFlow)
      super() { |_hash, _key| nil }
    elsif @parent
      super() { |_hash, _key| nil }
    else
      super()
      @parent = {}
    end
  end
end

CfgOptionalDefaultFlow.new(CfgOptionalDefaultFlow.new)
CfgOptionalDefaultFlow.new({})
CfgOptionalDefaultFlow.new

T.reveal_type(CfgOptionalDefaultFlow.new) # note: CfgOptionalDefaultFlow

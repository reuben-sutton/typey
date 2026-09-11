# typed: true
# conformance: cfg

class CfgMutableAccessorIvar
  attr_accessor :debug_mode

  def initialize
    @debug_mode = false
  end

  def check
    if @debug_mode
      "debug"
    else
      "normal"
    end
  end
end

T.reveal_type(CfgMutableAccessorIvar.new.check) # note: String

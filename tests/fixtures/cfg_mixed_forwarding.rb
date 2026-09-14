# typed: true

class CfgMixedForwarding
  def self.target(value, ...)
    value
  end

  def self.wrapper(name, ...)
    target(name, ...)
  end
end

T.reveal_type(CfgMixedForwarding.wrapper("value")) # note: Revealed type: `String`

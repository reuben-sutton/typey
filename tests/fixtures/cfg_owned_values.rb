# typed: true

CFG_OWNED_CONSTANT = "constant"
$cfg_owned_global = :global

class CfgOwnedValues
  @@kind = "kind"

  def initialize
    @value = 1
  end

  def value
    [nil, true, false, 1, 1.0, "string", :symbol, /pattern/, @value, @@kind, self,
     CFG_OWNED_CONSTANT, $cfg_owned_global]
  end

  def hash_value
    {one: 1, **{two: "two"}}
  end
end

CfgOwnedValues.new.value
CfgOwnedValues.new.hash_value

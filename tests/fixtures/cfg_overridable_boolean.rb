# typed: true
# conformance: cfg

class CfgOverridableBooleanBase
  def flag
    true
  end

  def choose
    flag ? "yes" : "no"
  end
end

class CfgOverridableBooleanChild < CfgOverridableBooleanBase
  def flag
    false
  end
end

T.reveal_type(CfgOverridableBooleanBase.new.choose) # note: Revealed type: `String`

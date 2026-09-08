class CfgCaseBody
  #: (Integer) -> String
  def describe(value)
    case value
    when 0
      "zero"
    when 1
      "one"
    else
      "other"
    end
  end
end

class CfgCaseBase
end

class CfgCaseChild < CfgCaseBase
  #: () -> Integer
  def child_only
    1
  end
end

class CfgCaseNarrowing
  #: (CfgCaseBase) -> String
  def narrow(value)
    case value
    when CfgCaseChild
      value.child_only.to_s
    else
      value.to_s
    end
  end
end

T.reveal_type(CfgCaseBody.new.describe(1)) # note: Revealed type: `String`
T.reveal_type(CfgCaseNarrowing.new.narrow(CfgCaseChild.new)) # note: Revealed type: `String`

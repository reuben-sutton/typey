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

T.reveal_type(CfgCaseBody.new.describe(1)) # note: Revealed type: `String`

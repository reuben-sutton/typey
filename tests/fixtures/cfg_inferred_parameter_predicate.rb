# typed: true

class CfgInferredParameterPredicate
  def value
    1
  end

  def *(other)
    if CfgInferredParameterPredicate === other
      other.value
    else
      other
    end
  end
end

CfgInferredParameterPredicate.new * 2

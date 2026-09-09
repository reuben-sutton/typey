class CfgUnionImplicitSelfBase
  private
    def private_value
      1
    end

  public
  def value_from_self
    if is_a?(CfgUnionImplicitSelfA) || is_a?(CfgUnionImplicitSelfB)
      [value, private_value]
    else
      "fallback"
    end
  end
end

class CfgUnionImplicitSelfA < CfgUnionImplicitSelfBase
  def value
    "a"
  end
end

class CfgUnionImplicitSelfB < CfgUnionImplicitSelfBase
  def value
    1
  end
end

T.reveal_type(CfgUnionImplicitSelfA.new.value_from_self) # note: Revealed type: T::Array[T.any(Integer, String)]

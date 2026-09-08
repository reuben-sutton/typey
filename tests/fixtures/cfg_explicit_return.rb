class CfgExplicitReturn
  #: (T::Boolean) -> String
  def value(flag)
    if flag
      return "yes"
    end
    "no"
  end
end

T.reveal_type(CfgExplicitReturn.new.value(true)) # note: Revealed type: `String`

class CfgHirPredicate
  #: (String?) -> String
  def nil_check(value)
    if value.nil?
      "nil"
    else
      value.upcase
    end
  end

  #: (Object) -> String
  def type_check(value)
    if value.is_a?(String)
      value.upcase
    else
      "not string"
    end
  end
end

CfgHirPredicate.new.nil_check(nil)

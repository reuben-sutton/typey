# typed: true

class CfgLogicalTypeNarrowingBase
end

class CfgLogicalTypeNarrowingLeft < CfgLogicalTypeNarrowingBase
  def shared
  end
end

class CfgLogicalTypeNarrowingRight < CfgLogicalTypeNarrowingBase
  def shared
  end
end

class CfgLogicalTypeNarrowing
  #: (CfgLogicalTypeNarrowingBase?) -> void
  def check(value)
    if value.is_a?(CfgLogicalTypeNarrowingLeft) || value.is_a?(CfgLogicalTypeNarrowingRight)
      value.shared
    end
  end
end

# typed: true

class CfgRunnable
  def name
    "fixture"
  end
end

class CfgOther
  def path
    #: self as CfgRunnable
    name
  end
end

# typed: true

class SystemExit < Exception
end

class CfgRescueNoreturn
  #: () -> bot
  def explicitly_terminate
    exit(1)
  end

  def terminate
    exit(1)
  end

  #: -> String
  def rescued
    terminate
  rescue SystemExit
    "recovered"
  end

  #: -> String
  def rescued_from_explicit
    explicitly_terminate
  rescue SystemExit
    "recovered"
  end
end

T.reveal_type(CfgRescueNoreturn.new.rescued) # note: String
T.reveal_type(CfgRescueNoreturn.new.rescued_from_explicit) # note: String

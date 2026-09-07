# typed: true

module ReadsHostConfig
  def value
    @config.upcase
  end
end

module SharedAncestor
end

class HostConfig
  include ReadsHostConfig
  include SharedAncestor

  def initialize
    @config = "ready"
  end
end

class UnrelatedSharedAncestor
  include SharedAncestor

  def initialize
    @config = {}
  end
end

T.reveal_type(HostConfig.new.value) # note: String

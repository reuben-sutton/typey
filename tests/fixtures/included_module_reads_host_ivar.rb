# typed: true

module ReadsHostState
  def value
    @state.upcase
  end
end

class HostState
  include ReadsHostState

  def initialize
    @state = "ready"
  end
end

T.reveal_type(HostState.new.value) # note: String

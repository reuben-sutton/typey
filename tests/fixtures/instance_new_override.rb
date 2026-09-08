# typed: true

class InstanceNewOverride
  def new(value)
    value.to_s
  end

  def check
    T.reveal_type(self.new(1)) # note: Revealed type: `String`
  end
end

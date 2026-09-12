# typed: true

class SafeNavigationMutableAccessor
  attr_accessor :value

  def initialize
    @value = Object.new
  end

  def render
    value&.to_s
  end
end

T.reveal_type(SafeNavigationMutableAccessor.new.render) # note: T.nilable(String)

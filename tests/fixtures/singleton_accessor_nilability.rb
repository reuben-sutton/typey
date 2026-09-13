# typed: true

class Settings
  class << self
    attr_accessor :value
  end

  def self.configure
    self.value = "configured"
  end
end

T.reveal_type(Settings.value) # note: T.nilable(String)

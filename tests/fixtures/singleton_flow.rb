module Extensions
  def extra
    :extra
  end
end

class Extended
  extend Extensions

  class << self
    def singleton_value
      "singleton"
    end
  end
end

T.reveal_type(Extended.extra) # note: Symbol
T.reveal_type(Extended.singleton_value) # note: String

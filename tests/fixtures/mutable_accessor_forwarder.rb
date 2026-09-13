# typed: true

class MutableAccessorForwarder
  class << self
    attr_accessor :value

    def forwarded
      value
    end

    def use
      forwarded&.to_s
    end
  end

  self.value = "text"
end

T.reveal_type(MutableAccessorForwarder.use) # note: T.nilable(String)

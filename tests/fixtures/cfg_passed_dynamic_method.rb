# typed: true

class PassedDynamicMethod
  class << self
    def install(&block)
      define_method(:run, &block)
    end
  end

  def only_instance
    "ok"
  end
end

PassedDynamicMethod.install do
  only_instance
end

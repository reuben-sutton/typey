# typed: true

class PassedSingletonDynamicMethod
  class << self
    def install(&block)
      define_singleton_method(:run, &block)
    end

    def only_class
      "ok"
    end
  end
end

PassedSingletonDynamicMethod.install do
  only_class
end

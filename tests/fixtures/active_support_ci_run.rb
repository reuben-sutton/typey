# typed: true

module ActiveSupport
  class ContinuousIntegration
    def step(name)
      name
    end

    class << self
      def run(&block)
      end
    end
  end
end

ActiveSupport::ContinuousIntegration.run do
  step "setup"
end

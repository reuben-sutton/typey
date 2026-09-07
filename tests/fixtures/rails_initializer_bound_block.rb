# typed: true

module Rails
  module Initializable
    module ClassMethods
      def initializer(name, options = {}, &block)
      end
    end

    def self.included(base)
      base.extend ClassMethods
    end
  end
end

class EngineBase
  include Rails::Initializable

  def instance_only
    "instance"
  end
end

class ExampleEngine < EngineBase
  initializer "example" do |app|
    instance_only
  end
end

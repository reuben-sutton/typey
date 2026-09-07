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

class FirstEngineBase
  include Rails::Initializable

  def first_only
    "first"
  end
end

class SecondEngineBase
  include Rails::Initializable

  def second_only
    "second"
  end
end

class FirstEngine < FirstEngineBase
  initializer "first" do
    first_only
  end
end

class SecondEngine < SecondEngineBase
  initializer "second" do
    second_only
  end
end

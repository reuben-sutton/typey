module ActiveSupport
  module Concern
  end
end

module ExampleConcern
  extend ActiveSupport::Concern

  module ClassMethods
    def install
      before_save -> { send(:value) } if respond_to?(:before_save)
    end
  end
end

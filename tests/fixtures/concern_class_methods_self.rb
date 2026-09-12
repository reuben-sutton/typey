module ActiveSupport
  module Concern
  end
end

module ExampleConcern
  extend ActiveSupport::Concern

  module ClassMethods
    def install
      T.reveal_type(self) # note: Revealed type: `T.untyped`
      before_save -> { send(:value) } if respond_to?(:before_save)
    end
  end
end

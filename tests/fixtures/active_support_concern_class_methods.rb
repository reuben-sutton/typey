# typed: true

module ActiveSupport
  module Concern
  end
end

module ExampleConcern
  extend ActiveSupport::Concern

  module ClassMethods
    def class_only
      "class"
    end
  end

  def instance_only
    "instance"
  end
end

class ExampleHost
  include ExampleConcern

  T.reveal_type(class_only) # note: Revealed type: `String`

  def use_instance_method
    T.reveal_type(instance_only) # note: Revealed type: `String`
  end
end

T.reveal_type(ExampleHost.class_only) # note: Revealed type: `String`
T.reveal_type(ExampleHost.new.use_instance_method) # note: Revealed type: `String`

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

  class_only

  def use_instance_method
    instance_only
  end
end

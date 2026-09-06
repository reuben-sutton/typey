# typed: true

module Kernel
  def default_kernel_method
    "ok"
  end
end

class Object
  include Kernel
end

class DefaultObjectChild
end

DefaultObjectChild.new.default_kernel_method

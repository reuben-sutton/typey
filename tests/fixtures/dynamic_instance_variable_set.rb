# typed: true

module DynamicIvarConcern
  def self.extended(base)
    base.instance_variable_set(:@items, [])
  end

  def each_item
    T.reveal_type(@items) # note: T::Array[T.untyped]
    @items.each { |item| item }
  end
end

def opaque_dynamic_ivar_read(object)
  value = object.instance_variable_get(:@items)
  T.reveal_type(value) # note: T.untyped
  value.each { |item| item }
end

class DynamicIvarHost
  extend DynamicIvarConcern
end

T.reveal_type(DynamicIvarHost.each_item) # note: T::Array[T.untyped]

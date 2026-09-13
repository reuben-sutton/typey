# typed: true

class DynamicMethodProvider
  def method_missing(name, *arguments)
    "handled #{name}"
  end
end

def dynamic_method_call(provider)
  provider.generated_method(1, 2)
end

dynamic_method_call(DynamicMethodProvider.new)

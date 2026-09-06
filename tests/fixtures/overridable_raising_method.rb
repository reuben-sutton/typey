class BaseValue
  def value
    raise "abstract"
  end

  def use
    result = value
    return unless result

    result.to_s
  end
end

class ConcreteValue < BaseValue
  def value
    "value"
  end
end

class NullableValue < BaseValue
  def value
    nil
  end
end

BaseValue.new.use
ConcreteValue.new.use
NullableValue.new.use

def always_raises
  raise "never"
end

def after_always_raises
  always_raises
  "unreachable" # error: This expression appears after an unconditional return
end

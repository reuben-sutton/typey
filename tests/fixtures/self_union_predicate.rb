# typed: true

class Parent
  def describe
    if is_a?(Child) || is_a?(OtherChild)
      children
    end
  end

  def fail_if_child
    if is_a?(Child) || is_a?(OtherChild)
      raise "not a parent"
    end
  end
end

class Child < Parent
  def children
    []
  end
end

class OtherChild < Parent
  def children
    []
  end
end

class CfgBodyTransfer
  def value
    local = 1
    @value = local
    @value.to_s
  end

  def collections
    values = [1, "two"]
    mapping = {"value" => values.first}
    [values, mapping]
  end

  def increment
    value = 1
    value += 2
    value
  end

  def dynamic_write
    mapping = {"old" => 1}
    mapping["new"] = 2
    mapping["new"]
  end

  def logical_write
    value = 1
    value &&= 2
    other = nil
    other &&= 3
    [value, other]
  end

  def keyword_target(value, label:)
    label
  end

  def keyword_call
    keyword_target(1, label: "ready")
  end

  #: (Integer, String) -> void
  def positional_target(one, two)
  end

  def fixed_splat_call
    positional_target(*[1, "ready"])
  end

  def dynamic_splat_call(values)
    positional_target(*values)
  end

  #: (String?) -> String
  def conditional(value)
    if value
      value.upcase
    else
      "missing"
    end
  end
end

CfgBodyTransfer.new.value

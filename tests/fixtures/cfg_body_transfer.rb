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

  def collection_splats
    values = [1, "two"]
    mapping = {"value" => 1, **{"other" => 2}}
    [[0, *values], mapping["value"]]
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

  def keyword_rest_target(**values)
    values
  end

  def keyword_splat_call
    values = {"count" => 1}
    keyword_rest_target(**values)
  end

  #: (String?) -> String?
  def safe_navigation(value)
    value&.to_s
  end

  def inline_block
    values = [1, 2]
    values.map { |value| value.to_s }
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
T.reveal_type(CfgBodyTransfer.new.safe_navigation("text")) # note: Revealed type: `T.nilable(String)`
T.reveal_type(CfgBodyTransfer.new.inline_block) # note: Revealed type: `T::Array[String]`

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
end

CfgBodyTransfer.new.value

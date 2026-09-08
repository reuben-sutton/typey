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

  def passed_block
    values = [1, 2]
    processor = ->(value) { value.to_s }
    values.map(&processor)
  end

  def symbol_block
    [1, 2].map(&:to_s)
  end

  def hash_map
    {"one" => 1}.map { |key, value| [key, value.to_s] }.to_h
  end

  def plain_begin
    begin
      value = 1
      value.to_s
    end
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

class CfgSuperBase
  #: () -> String
  def render
    "base"
  end
end

class CfgSuperChild < CfgSuperBase
  #: () -> String
  def render
    super
  end
end

class CfgForwardChild < CfgSuperBase
  #: (Integer) -> String
  def render(...)
    super(...)
  end
end

class CfgYield
  extend T::Sig
  sig { params(block: T.proc.params(value: Integer).returns(String)).returns(String) }
  def value(&block)
    yield(1)
  end
end

CfgBodyTransfer.new.value
T.reveal_type(CfgBodyTransfer.new.safe_navigation("text")) # note: Revealed type: `T.nilable(String)`
T.reveal_type(CfgBodyTransfer.new.inline_block) # note: Revealed type: `T::Array[String]`
T.reveal_type(CfgBodyTransfer.new.passed_block) # note: Revealed type: `T::Array[String]`
T.reveal_type(CfgBodyTransfer.new.symbol_block) # note: Revealed type: `T::Array[String]`
T.reveal_type(CfgBodyTransfer.new.hash_map) # note: Revealed type: `T::Hash[String, String]`
T.reveal_type(CfgBodyTransfer.new.plain_begin) # note: Revealed type: `String`
T.reveal_type(CfgSuperChild.new.render) # note: Revealed type: `String`
T.reveal_type(CfgForwardChild.new.render(1)) # note: Revealed type: `String`
T.reveal_type(CfgYield.new.value { |value| value.to_s }) # note: Revealed type: `String`

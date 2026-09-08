# typed: true

class CfgIndexSplatWrite
  extend T::Sig

  sig { params(key: String, value: String).returns(String) }
  def []=(key, value)
    value
  end

  sig { params(key: String).returns(String) }
  def [](key)
    "stored"
  end

  sig { returns(String) }
  def write
    self[*["key"]] = "value"
    self[*["key"]]
  end
end

T.reveal_type(CfgIndexSplatWrite.new.write) # note: String

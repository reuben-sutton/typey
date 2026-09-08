# typed: true

class CfgCallableUnion
  def call(flag)
    callback = if flag
      T.let(->(value) { value.to_s }, T.proc.params(value: String).returns(String))
    else
      T.let(->(value) { value.to_i }, T.proc.params(value: String).returns(Integer))
    end
    callback.call("value")
  end
end

T.reveal_type(CfgCallableUnion.new.call(true)) # note: T.any(Integer, String)

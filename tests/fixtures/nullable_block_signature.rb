module NullableBlockFactory
  sig do
    params(
      value: String,
      block: T.nilable(T.proc.params(value: String).void),
    ).returns(String)
  end
  def self.call(value, &block)
    value
  end
end

NullableBlockFactory.call("value")

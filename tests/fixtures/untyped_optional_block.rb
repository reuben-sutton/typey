def call_if_present(&block)
  return unless block

  block.call
end

call_if_present { "value" }

def apply_block(&block)
  block.call(1)
end

T.reveal_type(apply_block { |value| value.to_s }) # note: String

module OptionalBlockConsumer
  #: (?{ (String value) -> void }) -> void
  def self.consume(&block); end
end

def forward_block(&block)
  OptionalBlockConsumer.consume(&block)
end

forward_block { |value| value }

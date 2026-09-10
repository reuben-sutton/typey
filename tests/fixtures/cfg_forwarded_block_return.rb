def consume(&block)
  block.call(1)
end

def forward(&block)
  consume(&block)
end

T.reveal_type(forward { |value| value.to_s }) # note: Revealed type: `String`

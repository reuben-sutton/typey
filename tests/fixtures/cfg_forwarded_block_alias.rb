def sink(&block)
  [1].map(&block)
end

def forward_with_alias(&block)
  callback = block
  sink(&callback)
end

T.reveal_type(forward_with_alias { |value| value.to_s }) # note: Revealed type: `T::Array[String]`

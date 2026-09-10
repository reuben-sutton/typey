def sink(&block)
  block.call
end

def middle(&block)
  sink(&block)
end

def outer(&block)
  middle(&block)
end

T.reveal_type(outer { "nested" }) # note: Revealed type: `String`

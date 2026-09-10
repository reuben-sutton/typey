# typed: true

def optional_block_closure
  lambda do |&block|
    raise ArgumentError unless block
    block.call
  end
end

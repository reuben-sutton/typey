# typed: true

def optional_block_closure
  lambda do |target, value, &block|
    raise ArgumentError unless block
    target.instance_exec(target, block)
  end
end

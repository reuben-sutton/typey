# typed: true

module Tryable
  sig { params(blk: T.proc.returns(T.untyped)).returns(T.untyped) }
  def evaluate(&blk); end

  def try(&block)
    if block.arity == 0
      evaluate(&block)
    else
      yield self
    end
  end
end

class Object
  include Tryable
end

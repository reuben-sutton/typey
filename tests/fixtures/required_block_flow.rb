# typed: true

module Kernel
  extend T::Sig

  def block_given?
    true
  end

  sig do
    type_parameters(:X)
      .params(blk: T.proc.params(arg: T.untyped).returns(T.type_parameter(:X)))
      .returns(T.type_parameter(:X))
  end
  def yield_self(&blk)
    return 1 unless block_given?

    yield self
  end
end

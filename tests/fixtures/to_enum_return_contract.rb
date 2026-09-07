# typed: true

class Parameters
  extend T::Sig

  sig { params(block: T.untyped).returns(Parameters) }
  def select(&block) # error: Expected method `select` to return `Parameters`
    return to_enum(:select) unless block_given?

    self
  end
end

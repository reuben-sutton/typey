# typed: true

class PassedBlockContract
  extend T::Sig

  sig { params(block: T.proc.params(value: String).returns(String)).void }
  def check(&block)
    [1].map(&block) # error: Expected `T.proc.params(arg0: Integer).returns(T.anything)` but found `T.proc.params(arg0: String).returns(String)` for block argument
  end
end

PassedBlockContract.new.check { |value| value.to_s }

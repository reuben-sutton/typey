# typed: true

extend T::Sig

class GenericBlockArgument
  sig { params(block: T.proc.params(value: Integer).returns(String)).void }
  def check(block)
    ["value"].map(&block) # error: Expected `T.proc.params(arg0: String).returns(T.anything)` but found `T.proc.params(arg0: Integer).returns(String)` for block argument
  end
end

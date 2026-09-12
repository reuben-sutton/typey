# typed: true

class CatchNonlocalControl
  def self.ignore(throwable, &block)
    catch throwable do
      return block.call
    end
    nil
  end

  def self.run
    ignore(:done) { "value" }
    "after catch"
  end
end

T.reveal_type(CatchNonlocalControl.run) # note: `String`

class CfgMultiWriteTargets
  attr_accessor :value

  def initialize
    @value = 0
  end

  def []=(index, value)
    @value = value
  end

  def assign
    first, self.value = [1, 2]
    first
  end

  def indexed
    first, self[0] = [1, 2]
    first
  end

  def indexed_with_rights
    first, self[0], last = [1, 2, 3]
    last
  end
end

T.reveal_type(CfgMultiWriteTargets.new.assign) # note: Revealed type: Integer
T.reveal_type(CfgMultiWriteTargets.new.indexed) # note: Revealed type: Integer
T.reveal_type(CfgMultiWriteTargets.new.indexed_with_rights) # note: Revealed type: Integer

# typed: true

module AliasAssertions
  class << self
    def included(klass)
      klass.alias_method(:assert_not_nil, :refute_nil)
    end
  end
end

class AssertionBase
  def refute_nil(value)
    value
  end
end

AssertionBase.include(AliasAssertions)
value = AssertionBase.new.assert_not_nil("ok") # error: Method `assert_not_nil` does not exist
T.reveal_type(value) # note: Revealed type: `T.untyped`

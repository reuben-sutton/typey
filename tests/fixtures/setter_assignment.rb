# typed: true

class Writer
  extend T::Sig

  sig { params(value: Integer).returns(NilClass) }
  def value=(value)
  end
end

T.assert_type!(Writer.new.value = 1, Integer)

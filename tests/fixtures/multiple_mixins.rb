# typed: true

module FirstMixin
  def first_value
    "first"
  end
end

module SecondMixin
  def second_value
    "second"
  end
end

class MultipleMixinHost
  include FirstMixin, SecondMixin

  def values
    [first_value, second_value]
  end
end

T.reveal_type(MultipleMixinHost.new.values) # note: Revealed type: `T::Array[String]`

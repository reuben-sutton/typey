# typed: true

extend T::Sig

class SymbolBlockDispatch
  sig { params(values: T::Array[Integer]).void }
  def missing_method(values)
    values.map(&:even) # error: Method `even` does not exist on `Integer`
  end

  sig { params(values: T::Array[T.nilable(Integer)]).void }
  def nilable_receiver(values)
    values.map(&:even?) # error: Method `even?` does not exist on `NilClass` component of `T.nilable(Integer)`
  end
end

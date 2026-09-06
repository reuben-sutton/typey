# typed: true

class S
end

class A < S
end

extend T::Sig

sig { params(value: T.any(T.class_of(Integer), T.class_of(A))).void }
def only_subclasses_of_s(value)
  if value < S
    T.assert_type!(value, T.class_of(A))
  end
end

# typed: __STDLIB_INTERNAL

# Sorbet's runtime enum base is shipped outside the public Ruby stdlib RBIs.
# Keep the small, type-relevant surface here so enum subclasses receive the
# same attached-class return types as Sorbet.
class T::Enum
  extend T::Sig

  sig { returns(T::Array[T.attached_class]) }
  def self.values; end

  sig { params(serialized_val: T.untyped).returns(T.nilable(T.attached_class)) }
  def self.try_deserialize(serialized_val); end

  sig { params(serialized_val: T.untyped).returns(T.attached_class) }
  def self.from_serialized(serialized_val); end

  sig { returns(String) }
  def to_s; end

  sig { returns(String) }
  def inspect; end
end

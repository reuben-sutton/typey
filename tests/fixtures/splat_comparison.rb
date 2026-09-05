# typed: true

extend T::Sig

sig { params(one: Integer, two: String).void }
def fixed(one, two)
end

sig { params(values: Integer).void }
def accepts_rest(*values)
end

sig { params(first: Integer, second: String).void }
def fixed_keywords(first:, second:)
end

sig { returns(T::Array[T.untyped]) }
def dynamic_positional
  T::Array[T.untyped].new
end

sig { returns(T::Hash[Symbol, T.untyped]) }
def dynamic_keywords
  T::Hash[Symbol, T.untyped].new
end

# Rest parameters themselves are supported.
accepts_rest(1, 2, 3)

# A literal has a statically known shape and can be expanded.
fixed(*[1, "two"])

# These are the dynamic splats Sorbet documents as unsupported.
fixed(*dynamic_positional) # error: Splats are only supported where the size of the array is known statically
fixed_keywords(**dynamic_keywords) # error: Keyword args with splats are only supported where the shape of the hash is known statically

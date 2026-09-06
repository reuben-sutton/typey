# typed: true

#: (T::Range[Integer]) -> void
def accepts_integer_range(range)
end

accepts_integer_range(0...1)
accepts_integer_range("a"...1) # error: Expected `T::Range[Integer]`, but found `Range[String, Integer]`

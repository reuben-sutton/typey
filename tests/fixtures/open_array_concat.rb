# typed: true

values = []
values.concat(["value"])
values.unshift("first")
T.reveal_type(values) # note: Revealed type: T::Array[String]

# A callback between initialization and the append must not erase the fact
# that the local array is still open for concrete writes.
#: (Array[String]) -> void
def options(values)
  opts = []
  mapped = values.map { |value| "'#{value}'" }
  opts.concat(mapped)
  opts << "--no-stdlib"
  T.reveal_type(opts) # note: Revealed type: T::Array[String]
end

options(["value"])

def map_values(values, &block)
  values.map(&block)
end

T.reveal_type(map_values([1], &:to_s)) # note: Revealed type: `T::Array[String]`

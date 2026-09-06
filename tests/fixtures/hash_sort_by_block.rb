values = {"a" => 1, "b" => 2}
sorted = values.sort_by { |_key, value| -value }

T.reveal_type(sorted) # note: T::Array[[String, Integer]]

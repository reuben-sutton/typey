value = T.let(T.unsafe(nil), T.any(String, Symbol))

case value
when :same_as_pretty_output
  value = "pretty"
when Symbol
  raise "invalid symbol"
end

T.reveal_type(value) # note: String

# typed: true

next_value = lambda do
  next "lambda next"
  "unreachable"
end
T.reveal_type(next_value.call) # note: String

break_value = lambda do
  break 7
  "unreachable"
end
T.reveal_type(break_value.call) # note: T.untyped

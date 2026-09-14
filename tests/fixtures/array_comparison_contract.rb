# typed: true

#: -> Integer
def compare_metadata # error: Expected method `compare_metadata` to return `Integer`, but found `T.nilable(Integer)`
  result = [nil] <=> ["value"]
  T.reveal_type(result) # note: T.nilable(Integer)
end

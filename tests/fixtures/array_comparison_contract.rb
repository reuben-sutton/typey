# typed: true

#: -> Integer
def compare_metadata
  [nil] <=> ["value"] # error: Expected method `compare_metadata` to return `Integer`, but found `T.nilable(Integer)`
end

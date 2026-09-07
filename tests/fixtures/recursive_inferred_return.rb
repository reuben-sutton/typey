# typed: true

T.reveal_type(recursive_wrap("text")) # note: T::Array[Object]

def recursive_wrap(value)
  [recursive_wrap(value)]
end

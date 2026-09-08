# typed: true

#: (String | Array[String]) -> Array[String]
def coerce_command(command)
  result = Array(command)
  T.reveal_type(result) # note: T::Array[String]
  result
end

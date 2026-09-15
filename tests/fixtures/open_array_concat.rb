# typed: true

values = []
values.concat(["value"])
values.unshift("first")
T.reveal_type(values) # note: Revealed type: T::Array[String]

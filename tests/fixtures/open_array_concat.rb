# typed: true

values = []
values.concat(["value"])
T.reveal_type(values) # note: Revealed type: T::Array[String]

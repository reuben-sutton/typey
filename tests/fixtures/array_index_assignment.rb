# typed: true

lines = "one\ntwo".lines
T.reveal_type(lines[0] = "updated") # note: Revealed type: String
T.reveal_type(lines[0..1] = []) # note: Revealed type: T::Array[String]
T.reveal_type(lines[0..1] = ["updated"]) # note: Revealed type: T::Array[String]

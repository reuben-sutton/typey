# typed: true

parts = "root/child".split("/")
parent = T.must(parts[0...-1])
T.reveal_type(parent) # note: T::Array[String]

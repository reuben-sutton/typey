# Generic collection methods must use the inferred block result type.
values = [1, 2].map { |value| value.to_s }
T.reveal_type(values) # note: T::Array[String]

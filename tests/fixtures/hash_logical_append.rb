# typed: true

values = {} #: Hash[String, Array[String]]
T.reveal_type(values["key"] ||= []) # note: Revealed type: T::Array[String]
(values["key"] ||= []) << "value"

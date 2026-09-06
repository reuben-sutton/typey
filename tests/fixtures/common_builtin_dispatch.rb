# typed: true

module Envelope
  class Payload
    sig { returns(String) }
    def text
      "text"
    end
  end

  payload = T.let(T.unsafe(nil), Payload)
  T.reveal_type(payload.text) # note: String
end

module First
  class Shared
    sig { returns(String) }
    def label
      "first"
    end
  end

  value = T.unsafe(nil) #: Shared
  T.reveal_type(value.label) # note: String
end

module Second
  class Shared; end
end

T.reveal_type("prefix-value".delete_prefix("prefix-")) # note: String
T.reveal_type("value".inspect) # note: String
T.reveal_type(+"value") # note: String
T.reveal_type("value".<<("!")) # note: String
T.reveal_type([1, 2].freeze) # note: T::Array[Integer]
T.reveal_type({"value" => 1}.freeze) # note: T::Hash[String, Integer]
T.reveal_type(!true) # note: T::Boolean
T.reveal_type([1, 2].dup) # note: T::Array[Integer]
T.reveal_type({"value" => 1}.dup) # note: T::Hash[String, Integer]

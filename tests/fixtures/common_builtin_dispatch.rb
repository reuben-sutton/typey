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

T.reveal_type("prefix-value".delete_prefix("prefix-")) # note: String
T.reveal_type("value".inspect) # note: String
T.reveal_type([1, 2].freeze) # note: T::Array[Integer]
T.reveal_type({"value" => 1}.freeze) # note: T::Hash[String, Integer]

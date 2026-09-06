# typed: true

T.reveal_type(Random.alphanumeric(10, chars: ["a"])) # note: String
T.reveal_type(SecureRandom.alphanumeric(10, chars: ["a"])) # note: String
Random.alphanumeric("ten", chars: ["a"]) # error: Expected `T.nilable(Integer)`, but found `String`

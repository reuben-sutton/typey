# typed: true

T.reveal_type("value".hash) # note: Revealed type: `Integer`
T.reveal_type(ENV["VALUE"]) # note: Revealed type: `T.nilable(String)`

enumerator = [1].each
T.reveal_type(enumerator.map { |value| value.to_s }) # note: Revealed type: `T::Array[String]`

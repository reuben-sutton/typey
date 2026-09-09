# typed: true

value = T.let(nil, T.nilable(String))
result = value&.to_s #: as !nil
T.reveal_type(result) # note: String

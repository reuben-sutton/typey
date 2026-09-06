# typed: true

class Encoding < Object
  ASCII_8BIT = T.let(T.unsafe(nil), Encoding)
end

#: (Encoding) -> void
def accept_encoding(value); end

accept_encoding(Encoding::ASCII_8BIT)

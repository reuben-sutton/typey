# typed: true

sig { params(symbol: Symbol).returns(String) }
def symbol_name(symbol)
  symbol.name
end

T.reveal_type(symbol_name(:version)) # note: String

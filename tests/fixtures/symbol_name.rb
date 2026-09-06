# typed: true

sig { params(symbol: Symbol).returns(String) }
def symbol_name(symbol)
  symbol.name
end

symbol_name(:version)

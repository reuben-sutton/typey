class CfgSymbolBlock
  #: (Array[String]) -> Array[String]
  def upcase_all(values)
    values.map(&:upcase)
  end
end

T.reveal_type(CfgSymbolBlock.new.upcase_all(["ready"])) # note: Revealed type: `T::Array[String]`

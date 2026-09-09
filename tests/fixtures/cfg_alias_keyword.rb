class CfgAliasKeyword
  def original(value)
    value
  end

  alias renamed original
end

T.reveal_type(CfgAliasKeyword.new.renamed("value")) # note: Revealed type: `String`

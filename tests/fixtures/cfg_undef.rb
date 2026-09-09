# typed: true

class CfgUndef
  def removed
    1
  end

  undef :removed

  def kept
    "ok"
  end
end

T.reveal_type(CfgUndef.new.kept) # note: Revealed type: `String`

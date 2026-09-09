class CfgUnresolvedSuper
  def value
    super
  end
end

T.reveal_type(CfgUnresolvedSuper.new.value) # note: Revealed type: T.untyped

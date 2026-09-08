class CfgForBody
  def values
    result = nil
    for item in [1, 2]
      result = item
    end
    result
  end
end

T.reveal_type(CfgForBody.new.values) # note: Revealed type: `T.nilable(Integer)`

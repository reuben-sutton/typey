class CfgExceptionTransfer
  def rescued
    begin
      raise "boom"
    rescue StandardError => error
      error
    end
  end

  def bare_rescue
    begin
      raise "boom"
    rescue
      "recovered"
    end
  end
end

T.reveal_type(CfgExceptionTransfer.new.rescued) # note: Revealed type: `StandardError`
T.reveal_type(CfgExceptionTransfer.new.bare_rescue) # note: Revealed type: `String`

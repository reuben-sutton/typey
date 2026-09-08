class CfgEnsureTransfer
  def normal
    begin
      "value"
    ensure
      "cleanup"
    end
  end

  def rescued
    begin
      raise "boom"
    rescue StandardError
      "recovered"
    ensure
      "cleanup"
    end
  end

  def escaped
    begin
      raise "boom"
    ensure
      "cleanup"
    end
  end

  def writes_after_ensure
    value = nil
    begin
      "body"
    ensure
      value = "cleanup"
    end
    value
  end
end

T.reveal_type(CfgEnsureTransfer.new.normal) # note: Revealed type: `String`
T.reveal_type(CfgEnsureTransfer.new.rescued) # note: Revealed type: `String`
T.reveal_type(CfgEnsureTransfer.new.escaped) # note: Revealed type: `T.noreturn`
T.reveal_type(CfgEnsureTransfer.new.writes_after_ensure) # note: Revealed type: `String`

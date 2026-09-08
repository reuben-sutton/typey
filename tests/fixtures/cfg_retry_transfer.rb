class CfgRetryTransfer
  def retry_once
    attempts = 0
    begin
      attempts += 1
      if attempts == 1
        raise "boom"
      end
      "done"
    rescue StandardError
      if attempts == 1
        retry
      end
      "recovered"
    end
  end
end

T.reveal_type(CfgRetryTransfer.new.retry_once) # note: Revealed type: `String`

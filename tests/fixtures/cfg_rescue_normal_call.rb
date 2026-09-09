# typed: true

class CfgRescueNormalCall
  def value
    begin
      "normal"
    rescue StandardError
      "recovered".upcase
    end
  end
end

T.reveal_type(CfgRescueNormalCall.new.value) # note: Revealed type: `String`

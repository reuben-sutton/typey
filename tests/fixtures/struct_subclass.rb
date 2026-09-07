# typed: true

class Result < Struct.new(:status_code, :message)
  def success?
    !failure?
  end

  def failure?
    status_code.start_with?("5.")
  end
end

result = Result.new("200", "ok")
Result.new("only") # error: Not enough arguments provided
T.reveal_type(result.status_code) # note: Revealed type: `String`
T.reveal_type(result.message) # note: Revealed type: `String`
result.status_code.start_with?("2.")

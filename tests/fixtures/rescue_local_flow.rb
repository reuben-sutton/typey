# typed: true

def rescue_local_flow
  value = nil

  begin
    "value".upcase
  rescue StandardError
    value = []
  end

  if value
    value.first
  else
    :none
  end
end

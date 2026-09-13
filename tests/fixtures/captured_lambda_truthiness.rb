# typed: true

def captured_lambda_truthiness
  handled = false
  handler = -> { handled = true }

  if handled
    :handled
  else
    :not_handled
  end

  handler
end

def captured_lambda_nilability
  errors = nil
  handler = -> { errors ||= [] }

  if errors
    errors.first
  else
    :none
  end

  handler
end

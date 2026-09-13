# typed: true

def raise_with_cause
  error = RuntimeError.new("cause")
  raise RuntimeError, "unexpected", error.backtrace, cause: error
end

T.reveal_type(raise_with_cause) # note: T.noreturn

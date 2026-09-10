# typed: true
# conformance: cfg

class CfgTransactionalFallback
  value = 1
  yield # error: Invalid yield
  T.reveal_type(value) # note: Integer
end

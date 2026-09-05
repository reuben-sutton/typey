value = 1
matched = nil
case value
in Integer
  T.reveal_type(value) # note: Integer
  matched = value.to_s
else
  matched = nil
end
T.reveal_type(matched) # note: T.nilable(String)

handled = begin
  raise "boom"
rescue StandardError => error
  error.to_s
ensure
  cleanup = 1
end
T.reveal_type(handled) # note: String
T.reveal_type(cleanup) # note: Integer

fallback = (raise "boom") rescue "fallback"
T.reveal_type(fallback) # note: String

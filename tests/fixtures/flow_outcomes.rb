def early(flag)
  if flag
    return "yes"
  end
  "no"
end

T.reveal_type(early(true)) # note: String

loop_value = while true
  break "done"
end
T.reveal_type(loop_value) # note: T.nilable(String)

for_value = for item in [1, 2]
  break item.to_s
end
T.reveal_type(for_value) # note: T.nilable(String)

next_value = while false
  next "ignored"
end
T.reveal_type(next_value) # note: NilClass

handled = begin
  raise "boom"
rescue StandardError
  "recovered"
ensure
  cleanup = :ok
end
T.reveal_type(handled) # note: String
T.reveal_type(cleanup) # note: Symbol

def retrying
  attempts = 0
  begin
    attempts = attempts + 1
    if attempts < 2
      raise "again"
    end
  rescue StandardError
    retry
  end
  "done"
end

T.reveal_type(retrying) # note: String

mapped_with_break = [1].map do |item|
  if item == 1
    break :stopped
  end
  item.to_s
end
T.reveal_type(mapped_with_break) # note: T::Array[String]

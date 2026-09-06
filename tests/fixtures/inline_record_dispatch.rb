# typed: true

#: -> { value: Integer, label: String }
def record_value
  T.unsafe(nil)
end

record = record_value
T.reveal_type(record[:value]) # note: Integer
T.reveal_type(record[:label]) # note: String

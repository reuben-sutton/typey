# typed: true

#: (String?) -> String?
def logical_value(value)
  value && value.to_s
end

T.reveal_type(logical_value(nil))
T.reveal_type(logical_value("text"))
T.reveal_type(nil && "text")
T.reveal_type(nil)
T.reveal_type(false && "text")

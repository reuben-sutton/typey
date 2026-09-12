# typed: true

#: (String?) -> String?
def logical_value(value)
  value && value.to_s
end

T.reveal_type(logical_value(nil)) # note: T.nilable(String)
T.reveal_type(logical_value("text")) # note: T.nilable(String)
T.reveal_type(nil && "text") # note: NilClass
T.reveal_type(nil) # note: NilClass
T.reveal_type(false && "text") # note: FalseClass

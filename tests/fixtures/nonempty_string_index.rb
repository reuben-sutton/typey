# typed: true

value = "value" #: String
if !value.empty?
  T.reveal_type(value[0]) # note: String
end

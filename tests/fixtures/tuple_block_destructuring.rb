# typed: true

pairs = [] #: Array[[String, Integer]]
pairs.each do |name, count|
  T.reveal_type(name) # note: String
  T.reveal_type(count) # note: Integer
end

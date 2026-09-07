# typed: true

loop do
  "value".upcase
  throw(:done)
end

mystery do # error: Method `mystery` does not exist on `Object`
  "value".upcase
  break
end

# typed: true

def maybe_header
  if rand > 0
    "Content-Length: 2"
  end
end

header = maybe_header
raise "bad headers" unless header&.match?(/Content-Length: /)

T.reveal_type(header) # note: String
T.reveal_type(header.slice(16, 1)) # note: T.nilable(String)

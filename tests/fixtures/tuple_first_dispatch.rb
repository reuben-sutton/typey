# typed: true

location = Object.const_source_location(T.unsafe(Object).to_s)&.first
T.reveal_type(Object.const_source_location("String")) # note: Revealed type: `T.nilable([String, Integer])`
T.reveal_type(location) # note: Revealed type: `T.nilable(String)`
if location
  location.start_with?("file")
end

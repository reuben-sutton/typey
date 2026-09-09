# typed: true

location = Object.const_source_location("Object")&.first
T.reveal_type(location) # note: Revealed type: `T.nilable(String)`
location&.start_with?("/tmp")

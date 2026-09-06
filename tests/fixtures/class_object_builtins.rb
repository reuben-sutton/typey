# typed: true

class Location; end

T.reveal_type(Location === Object.new) # note: T::Boolean
T.reveal_type(Object.const_source_location("String")) # note: T.nilable([String, Integer])
T.reveal_type(Kernel.exit(1)) # note: T.noreturn

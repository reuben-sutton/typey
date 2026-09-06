# typed: true

class Box
  #: String
  attr_accessor :value
end

box = Box.new
box.value = "value"
T.reveal_type(box.value) # note: String

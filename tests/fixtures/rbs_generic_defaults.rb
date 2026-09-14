# typed: true

#: [Elem = String]
class Box
  #: -> Elem
  def value
    "value"
  end
end

T.reveal_type(Box.new.value) # note: Revealed type: `String`

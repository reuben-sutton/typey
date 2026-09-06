# typed: true

class Card
  #: -> String
  def html = "html"
end

T.reveal_type([:translate_all, :translate_last].map(&:inspect)) # note: T::Array[String]
T.reveal_type([Card.new].map(&:html)) # note: T::Array[String]

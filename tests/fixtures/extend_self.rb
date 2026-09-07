# typed: true

module SelfExtended
  extend self

  def value
    "value"
  end
end

T.reveal_type(SelfExtended.value) # note: String

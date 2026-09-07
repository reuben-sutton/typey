# typed: true

extend T::Sig

class Holder
  extend T::Sig

  sig { void }
  def initialize
    @value = T.let(T.unsafe(nil), T.any(String, Integer))
  end

  sig { returns(String) }
  def string_value
    if String === @value
      T.reveal_type(@value) # note: Revealed type: `String`
      @value.upcase
    else
      ""
    end
  end
end

Holder.new.string_value

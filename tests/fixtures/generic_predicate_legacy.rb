# typed: true

class GenericPredicateLegacy
  extend T::Sig

  sig { type_parameters(:V).params(value: T.type_parameter(:V)).returns(String) }
  def self.convert(value)
    if value.is_a?(Hash)
      value.to_hash
      "hash"
    else
      "other"
    end
  end
end

T.reveal_type(GenericPredicateLegacy.convert({})) # note: String

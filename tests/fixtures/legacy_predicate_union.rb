# typed: true

class Object
  def to_query(key)
    "#{key}"
  end
end

class LegacyPredicateUnion
  extend T::Sig

  sig { type_parameters(:V).params(value: T.type_parameter(:V)).returns(String) }
  def self.convert(value)
    [value].filter_map { |element|
      next if (element.is_a?(Hash) || element.is_a?(Array)) && element.empty?
      element.to_query("key")
    }.join
  end
end

class GenericObjectProtocol
  extend T::Sig

  sig { type_parameters(:V).params(value: T.type_parameter(:V)).returns(String) }
  def self.string_value(value)
    value.to_s
  end
end

T.reveal_type(LegacyPredicateUnion.convert({})) # note: String
T.reveal_type(GenericObjectProtocol.string_value(Object.new)) # note: String

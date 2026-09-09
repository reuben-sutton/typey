# typed: true

extend T::Sig

sig { params(items: T::Array[[String, Integer]]).void }
def destructure_typed_tuple_call(items)
  first, _second = items.first #: as [String, Integer]
  T.reveal_type(first) # note: String
  first.upcase
end


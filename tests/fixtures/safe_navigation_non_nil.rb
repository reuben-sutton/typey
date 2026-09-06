# typed: true

extend T::Sig
sig { params(value: Integer).void }
def safe_navigation_on_integer(value)
  value&.to_s # error: Used `&.` operator on `Integer`, which can never be nil
end

safe_navigation_on_integer(1)

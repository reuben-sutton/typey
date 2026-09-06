# typed: true

if 1
  :reachable
else
  :unreachable # error: This code is unreachable
end

value = if true
  :reachable
else
  :expression_branch
end

T.assert_type!(value, Symbol)

def known_truthy_after_early_returns(value)
  if value
    if value
      :reachable
    else
      return false # error: This code is unreachable
    end
  else
    if value
      :reachable
    else
      return false # error: This code is unreachable
    end
  end

  if value
    :reachable
  else
    :unreachable # error: This code is unreachable
  end
end

class NilClass
  extend T::Sig

  sig { returns(TrueClass) }
  def blank?
    true
  end
end

if !nil.blank?
  :unreachable # error: This code is unreachable
end

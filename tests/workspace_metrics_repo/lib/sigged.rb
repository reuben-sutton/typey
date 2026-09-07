# typed: true

sig do
  params(
    value: T.any(String, Integer)
  ).returns(String)
end

TypeLike = T.type_alias { T.any(String, Integer) }

def render(value)
  value.to_s
end

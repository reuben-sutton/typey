class Box
  def initialize(value)
    @value = value
  end

  def value
    @value
  end
end

class Factory
  def self.from(value)
    value.to_s
  end
end

class Base
  def label(value)
    value.to_s
  end
end

class Derived < Base
end

T.reveal_type(Box.new(1).value) # note: Integer
T.reveal_type(Factory.from(1)) # note: String
T.reveal_type(Derived.new.label(1)) # note: String

items = [1, 2.0]
for item in items
  last = item
end
T.reveal_type(last) # note: T.any(Float, Integer, NilClass)

selected = nil
case last
when Integer
  selected = last.to_s
when Float
  selected = last.to_i
end
T.reveal_type(selected) # note: T.any(Integer, NilClass, String)

value = nil
while true
  value = 1
end
T.reveal_type(value) # note: T.nilable(Integer)

captured = nil
[1].each do |item|
  captured = item.to_s
end
T.reveal_type(captured) # note: T.nilable(String)

mapped = [1, 2].map { |item| item.to_s }
T.reveal_type(mapped) # note: T::Array[String]

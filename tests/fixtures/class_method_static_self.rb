# typed: true

class Parent
  def child
    1
  end

  def call
    child
  end
end

class Child < Parent
  def child
    "child"
  end
end

T.reveal_type(Parent.new.call) # note: Integer

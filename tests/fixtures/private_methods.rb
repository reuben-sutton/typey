# typed: true

class Parent
  extend T::Sig

  sig { returns(Parent) }
  def self.make
    new
  end

  sig { params(value: Parent).void }
  private_class_method def self.consume(value)
  end

  def self.inside
    self.consume(Parent.new)
  end
end

Parent.consume(Parent.new) # error: Non-private call to private method `consume`

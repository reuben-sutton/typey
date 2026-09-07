# typed: true

class Parent
  extend T::Helpers
  extend T::Sig

  abstract!

  sig { returns(T.nilable(T.attached_class)) } # error: `T.attached_class` may only be used in singleton methods on classes or instance methods on `has_attached_class!` modules
  def bad_sig
    nil
  end

  sig { returns(T.nilable(T.attached_class)) }
  def self.make
    nil
  end
end

class Child < Parent; end
class GrandChild < Child; end

T.reveal_type(Child.make) # note: Revealed type: `T.nilable(Child)`
T.reveal_type(GrandChild.make) # note: Revealed type: `T.nilable(GrandChild)`

T.reveal_type(T::Array[Integer].new) # note: Revealed type: `T::Array[Integer]`
T.reveal_type(Array.new) # note: Revealed type: `T::Array[T.untyped]`
T.reveal_type(File.new("foo", "r").first) # note: Revealed type: `T.nilable(String)`

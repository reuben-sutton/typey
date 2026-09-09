# typed: true

pairs = [["class A; end", "A"], ["class B; end", "B"]]
pairs.each do |source, name|
  T.reveal_type(source) # note: Revealed type: `T::Array[String]`
  T.reveal_type(name) # note: Revealed type: `T.untyped`
end

# typed: true

value = T.let(["file.rb"], T.nilable(T::Array[String]))
first = value&.first
T.reveal_type(first) # note: T.nilable(String)
if first
  T.reveal_type(first) # note: String
  first.start_with?("file")
end

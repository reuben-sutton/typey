# typed: true

value = T.let(["file.rb"], T.nilable(T::Array[String]))
first = value&.first
if first
  first.start_with?("file")
end

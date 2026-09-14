# typed: true

class FlatMapError
  #: String?
  attr_reader :file

  #: Set[String]
  attr_reader :files
end

errors = T.let([], T::Array[FlatMapError])
files = errors.flat_map { |error| [error.file, *error.files] }
T.reveal_type(files) # note: Revealed type: T::Array[T.nilable(String)]

# typed: true

class ArrayIndex
  #: (Array[String]) -> String
  def first(values) # error: Expected method `first` to return `String`, but found `T.nilable(String)`
    values[1]
  end
end

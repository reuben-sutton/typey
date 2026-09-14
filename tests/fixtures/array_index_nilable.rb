# typed: true

class ArrayIndex
  #: (Array[String]) -> String
  def first(values) # error: Expected method `first` to return `String`, but found `T.nilable(String)`
    T.reveal_type(values[1]) # note: T.nilable(String)
    values[1]
  end
end

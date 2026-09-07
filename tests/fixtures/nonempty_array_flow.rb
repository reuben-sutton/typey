# typed: true

sig { params(name: T.any(String, Symbol)).void }
def accepts_name(name); end

#: (T::Array[Symbol]) -> void
def forwards_name(names)
  return if names.empty?

  accepts_name(names.first)
end

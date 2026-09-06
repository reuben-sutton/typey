# typed: true

class KnownConstantOwner
  VALUE = 1
end

KnownConstantOwner::VALUE
KnownConstantOwner::Missing # error: Unable to resolve constant `KnownConstantOwner::Missing`
MissingConstant # error: Unable to resolve constant `MissingConstant`
T::Array[Integer]

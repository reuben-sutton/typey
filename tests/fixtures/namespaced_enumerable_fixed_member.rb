# typed: true

class GenericPackage
  #: String
  attr_reader :name
end

#: [Elem = GenericPackage]
class GenericPackageSet
  include Enumerable

  #: { (GenericPackage) -> untyped } -> untyped
  def each(&block)
    nil
  end

  #: -> Hash[String, String]
  def names
    to_h { |package| [package.name, package.name] }
  end
end

T.reveal_type(GenericPackageSet.new.names) # note: T::Hash[String, String]

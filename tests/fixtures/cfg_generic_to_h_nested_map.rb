# typed: true

class CfgGenericPackage
  #: -> String
  def name
    "package"
  end

  #: -> Array[String]
  def dependencies
    ["dependency"]
  end
end

class CfgGenericPackageSet
  #: (String) -> CfgGenericPackage?
  def fetch(name)
    nil
  end

  sig do
    type_parameters(:U, :V).params(
      blk: T.proc.params(arg0: CfgGenericPackage).returns([
        T.type_parameter(:U),
        T.type_parameter(:V)
      ])
    ).returns(T::Hash[T.type_parameter(:U), T.type_parameter(:V)])
  end
  def to_h(&blk)
    {}
  end
end

def cfg_generic_edges(package_set)
  package_set.to_h do |package|
    [
      package.name,
      package.dependencies.map { |dependency| package_set.fetch(dependency)&.name },
    ]
  end
end

T.reveal_type(cfg_generic_edges(CfgGenericPackageSet.new))

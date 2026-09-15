# typed: true

class ExplicitUntypedIvarBoundary
  def value
    @options = nil #: Hash[Symbol, untyped]?
    @options = {paths: []}
    @options[:paths].empty?
  end
end

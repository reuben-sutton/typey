# typed: true

class ForwardedBlockLegacy
  def self.pass(&block)
    consume(&block)
  end

  def self.consume
    yield 1
  end
end

ForwardedBlockLegacy.pass { |value| value.to_s }

class FilterRequiredParameterNames
  def self.call(parameters)
    names = parameters.filter_map { |type, name| name if type == :req }
    names << "&"
    names.join(", ")
  end
end

FilterRequiredParameterNames.call([[:req, :value], [:opt, :other]])

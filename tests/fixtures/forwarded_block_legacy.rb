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

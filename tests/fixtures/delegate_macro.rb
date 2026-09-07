# typed: true

class Backend
  def parse(value)
    value
  end
end

class Parser
  def self.delegate(*)
  end

  def backend
    Backend.new
  end

  delegate :parse, to: :backend
  delegate :name, to: :backend, prefix: :backend
end

Parser.new.parse("xml")
Parser.new.backend_name
Parser.new.missing
# error: Method `missing` does not exist on `Parser`

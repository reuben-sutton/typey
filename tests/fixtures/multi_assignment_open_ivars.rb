# typed: true

class OpenIvarState
  def initialize
    @filters, @silencers = [], []
  end

  def add_filter
    @filters << ->(line) { line.to_s }
    @silencers << ->(line) { line.to_s }
  end
end

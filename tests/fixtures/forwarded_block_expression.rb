class Builder
  def build(klass, &block)
    klass.new(&block)
  end
end

module GenericFactory
  def [](*types)
  end
end

class Factory
  extend GenericFactory

  #: (*Integer) -> String
  def self.[](*types)
    "direct"
  end
end

T.reveal_type(Factory[1]) # note: String

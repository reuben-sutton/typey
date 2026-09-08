# typed: true

class DynamicFormatterState
  class << self
    #: -> void
    def initialize_formats
      @formats = [] #: Array[String]
    end

    #: -> Array[String]
    def read_formats
      current = instance_variable_get(:@formats)
      T.reveal_type(current) # note: T::Array[String]
      current
    end
  end
end

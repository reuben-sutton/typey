# typed: true

module LSP
  class Error < StandardError; end

  class Diagnostic
    #: Integer
    attr_reader :code

    #: () -> void
    def initialize
      @code = 1
    end
  end

  class Error::Diagnostics < Error
    #: Array[Diagnostic]
    attr_reader :diagnostics

    #: (Array[Diagnostic]) -> void
    def initialize(diagnostics)
      @diagnostics = diagnostics
      super()
    end
  end
end

begin
  raise LSP::Error::Diagnostics.new([LSP::Diagnostic.new])
rescue LSP::Error::Diagnostics => error
  T.reveal_type(error) # note: LSP::Error::Diagnostics
  T.reveal_type(error.diagnostics) # note: T::Array[LSP::Diagnostic]
  error.diagnostics.each do |diagnostic|
    T.reveal_type(diagnostic.code) # note: Integer
  end
end

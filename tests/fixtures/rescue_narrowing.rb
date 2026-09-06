# typed: true

class Failure < StandardError
  #: Integer
  attr_reader :code

  #: () -> void
  def initialize
    @code = 1
    super()
  end
end

begin
  raise Failure.new
rescue Failure => error
  T.reveal_type(error.code) # note: Integer
end

# typed: true

module AnonymousFormatter
  def identifier
    "custom"
  end
end

formatter = Class.new do
  include AnonymousFormatter
end

T.reveal_type(formatter.new.identifier) # note: String

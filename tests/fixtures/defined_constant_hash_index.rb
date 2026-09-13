# typed: true

module DefinedConstantHashIndex
  unless defined?(TYPE_NAMES)
    TYPE_NAMES = {"Time" => "dateTime"}
  end

  T.reveal_type(TYPE_NAMES["Time"]) # note: String
end

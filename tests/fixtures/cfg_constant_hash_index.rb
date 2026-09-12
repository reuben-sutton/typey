# typed: true
# conformance: cfg

CFG_CONSTANT_HASH = {"Time" => "dateTime"}
T.reveal_type(CFG_CONSTANT_HASH["Time"]) # note: String

module CfgConstantHashIndex
  NAMES = {"Time" => "dateTime"}
  T.reveal_type(NAMES["Time"]) # note: String
end

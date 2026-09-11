# typed: true
# conformance: cfg

value = Proc.new { 1 }
T.reveal_type(value) # note: Revealed type: `Proc`
value.arity
value.call

parsers = {"text" => Proc.new { |value| value.to_s }}
if parser = parsers["text"]
  T.reveal_type(parser) # note: Revealed type: `Proc`
  parser.arity
  parser.call("value")
end

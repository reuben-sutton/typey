# typed: true

T.reveal_type(YAML.dump({"key" => "value"})) # note: Revealed type: `String`
T.reveal_type(YAML.load_file("config.yml")) # note: Revealed type: `T.untyped`

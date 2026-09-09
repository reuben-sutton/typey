# typed: true

T.reveal_type(YAML.dump({"key" => "value"}))
T.reveal_type(YAML.load_file("config.yml"))

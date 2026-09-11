# typed: true
# conformance: cfg

def cfg_ensure_local_initialization
  value = "value".upcase
ensure
  value&.to_s
end

T.reveal_type(cfg_ensure_local_initialization) # note: String

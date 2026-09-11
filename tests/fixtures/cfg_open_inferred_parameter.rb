# typed: true
# conformance: cfg

def cfg_open_inferred_parameter(ttl = nil, expires = nil, raw = false)
  if ttl && expires && expires > 0 && !raw
    ttl += 5
  end
  ttl
end

cfg_open_inferred_parameter(nil, nil, false)

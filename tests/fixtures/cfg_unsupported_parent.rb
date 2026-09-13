# typed: true
# conformance: cfg

BEGIN { T.reveal_type(1) } # note: Integer
T.reveal_type(2) # note: Integer

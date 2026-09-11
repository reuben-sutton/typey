# typed: true

value = Ractor[:typey_key]
T.reveal_type(value) # note: Revealed type: `T.untyped`
Ractor[:typey_key] = value

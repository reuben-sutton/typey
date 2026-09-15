# typed: true

match = "thing"
T.reveal_type(match[0]) # note: Revealed type: T.nilable(String)
T.reveal_type(match[0].upcase) # error: Method `upcase` does not exist on `NilClass` component of `T.nilable(String)`

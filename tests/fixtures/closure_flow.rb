stringify = ->(value) { "stringified" }
status = lambda { :ok }

T.reveal_type(stringify.call(1)) # note: String
T.reveal_type(status.call) # note: Symbol

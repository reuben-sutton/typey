# typed: true

value = 1
T.reveal_type("value=#{value.to_s}") # note: String
T.reveal_type(/value=#{value}/) # note: Regexp
T.reveal_type(:"value_#{value}") # note: Symbol
T.reveal_type(`echo #{value}`) # note: String

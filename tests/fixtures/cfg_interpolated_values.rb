# typed: true

value = 1
T.reveal_type("value=#{value.to_s}") # revealed: String
T.reveal_type(/value=#{value}/) # revealed: Regexp
T.reveal_type(:"value_#{value}") # revealed: Symbol
T.reveal_type(`echo #{value}`) # revealed: String

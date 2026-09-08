# typed: true

T.noreturn.to_s # error: Call to method `to_s` on `T.noreturn` mistakes a type for a value
T.untyped.to_s # error: Call to method `to_s` on `T.untyped` mistakes a type for a value
T.self_type.to_s # error: Call to method `to_s` on `T.untyped` mistakes a type for a value
T.class_of(Integer).to_s # error: Call to method `to_s` on `T.class_of(Integer)` mistakes a type for a value
T.proc.void + 1 # error: Call to method `+` on `T.proc.void` mistakes a type for a value

T.class_of.foo # error: Not enough arguments
T.class_of(Integer, String).foo # error: Too many arguments

T.reveal_type(T.untyped.valid?(nil)) # note: Revealed type: `T.untyped`

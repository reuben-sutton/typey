# typed: true

runtime_type = T.proc.params(value: String).returns(Integer)
runtime_type.call("value") # error: Method `call` does not exist on `T::Types::Proc`

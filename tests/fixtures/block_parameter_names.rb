extend T::Sig

sig { params(callback: T.proc.params(value: Integer).void).void }
def named_callback(&callback)
  callback.call("wrong") # error: Expected `Integer` but found `String` for argument `arg0
end

sig { params("&": T.proc.params(value: Integer).void).void }
def anonymous_callback(&)
end

anonymous_callback { |value| T.reveal_type(value) } # note: Integer

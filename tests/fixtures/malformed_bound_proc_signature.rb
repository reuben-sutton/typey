# typed: true

class CallbackRegistry
  extend T::Sig

  sig { params(callback: T.proc.bind(T.self_type)).returns(NilClass) } # error: Malformed T.proc: You must specify a return type
  def register(&callback); end
end

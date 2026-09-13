# typed: true

T.reveal_type(Module.new.module_eval { "module body" }) # note: String
T.reveal_type(Class.new.class_eval { 1 }) # note: Integer

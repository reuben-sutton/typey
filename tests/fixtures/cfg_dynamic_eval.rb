# typed: true

class DynamicEvalTarget
end

T.reveal_type(DynamicEvalTarget.class_eval { 1 }) # note: Integer

def run_dynamic_eval(klass, &block)
  klass.class_eval(&block)
end

run_dynamic_eval(DynamicEvalTarget) { "ok" }

def run_module_dynamic_eval(base, &block)
  if base.is_a?(Module)
    base.class_eval(&block)
  end
end

run_module_dynamic_eval(DynamicEvalTarget) { "module" }

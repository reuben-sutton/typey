# typed: true
# conformance: cfg

class Array
  #: (Integer) -> Array
  def cfg_to(position)
    if position >= 0
      self[0..position]
    else
      self[0..position]
    end
  end
end

class CfgActiveSupportPredicate
  extend T::Sig

  sig { type_parameters(:V).params(value: T.type_parameter(:V)).returns(String) }
  def self.hash_value(value)
    if value.is_a?(Hash)
      value.to_s
    else
      "other"
    end
  end
end

class CfgActiveSupportCasePattern
  #: (T.any(String, Regexp)) -> String
  def self.parse(value)
    case value
    when /ruby/
      value.to_s
    else
      value.to_s
    end
  end
end

class CfgActiveSupportOverridableBase
  def html_safe?
    false
  end
end

class CfgActiveSupportOverridableChild < CfgActiveSupportOverridableBase
  def html_safe?
    true
  end
end

def cfg_active_support_boolean(value)
  value.html_safe? ? "safe" : "escaped"
end

def cfg_active_support_proc_binding(proc_value)
  proc_value.binding
end

class CfgActiveSupportBlockForwarding
  def pass(&block)
    consume(&block)
  end

  def consume
    yield 1
  end
end

CfgActiveSupportBlockForwarding.new.pass { |value| value.to_s }

T.reveal_type([1].cfg_to(-1)) # note: `T::Array[T.untyped]`
T.reveal_type(CfgActiveSupportPredicate.hash_value({})) # note: `String`
T.reveal_type(CfgActiveSupportCasePattern.parse("ruby")) # note: `String`
T.reveal_type(cfg_active_support_boolean(CfgActiveSupportOverridableBase.new)) # note: `String`
T.reveal_type(cfg_active_support_proc_binding(-> { 1 })) # note: `Binding`

# typed: true

class CfgNamespacedCaseConstantKind
  Class = T.let(T.unsafe(nil), CfgNamespacedCaseConstantKind)
end

#: (CfgNamespacedCaseConstantKind) -> String
def cfg_namespaced_case_constant(kind)
  case kind
  when CfgNamespacedCaseConstantKind::Class
    "class".upcase
  else
    "other".upcase
  end
end

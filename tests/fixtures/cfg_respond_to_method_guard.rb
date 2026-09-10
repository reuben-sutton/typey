# typed: strict
# conformance: cfg

class CfgRespondToMethodGuard
end

value = CfgRespondToMethodGuard.new
if value.respond_to?(:name)
  value.name
end

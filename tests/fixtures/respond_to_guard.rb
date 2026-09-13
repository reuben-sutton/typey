# typed: true

class CapabilityTarget
end

target = CapabilityTarget.new
if target.respond_to?(:runtime_only)
  target.runtime_only
end

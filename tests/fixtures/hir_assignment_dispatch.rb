# typed: true

class HIRAssignmentDispatch
  @@class_value = 0
  HIR_CONSTANT = 0

  def initialize
    @value = 0
    @values = [0]
  end

  def run
    local = 1
    @value = local
    @@class_value ||= local
    $hir_assignment_global &&= local
    HIR_CONSTANT += local

    local += 1
    local &&= @value
    local ||= @value
    @value += local
    @value &&= local
    @value ||= local
    @@class_value += local
    $hir_assignment_global ||= local

    @values[0] = local
    @values[0] += local
    @values[0] &&= local
    @values[0] ||= local
    local
  end
end

HIRAssignmentDispatch.new.run

# typed: true

class CfgIvarOrAssignment
  #: -> String
  def value
    @value ||= "ready" #: String?
  end
end

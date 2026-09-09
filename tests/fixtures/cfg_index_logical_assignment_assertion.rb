# typed: true

class CfgIndexLogicalAssignmentAssertion
  def value
    @values = {} #: Hash[String, String?]
    @values["key"] ||= "default".upcase #: as !nil
  end
end

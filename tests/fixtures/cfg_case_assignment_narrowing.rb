# typed: true

class CfgCaseAssignmentNarrowing
  #: (T.any(String, Integer)) -> Integer
  def self.length_of(value)
    case (current = value)
    when String
      T.reveal_type(current) # note: String
      current.length
    else
      0
    end
  end
end

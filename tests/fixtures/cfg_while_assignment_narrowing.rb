# typed: true

class CfgWhileAssignmentNarrowing
  #: -> String?
  def next_value
    nil
  end

  #: -> String
  def value
    while (current = next_value)
      current.upcase
    end
    "done"
  end
end

T.reveal_type(CfgWhileAssignmentNarrowing.new.value) # note: String

# typed: strict

class CaseNarrowingLocation
  attr_reader :file

  #: (BasicObject other) -> Integer?
  def <=>(other)
    return unless CaseNarrowingLocation === other

    other.file
    0
  end

  #: (T.any(CaseNarrowingLocation, String)) -> Integer
  def classify(other)
    if CaseNarrowingLocation === other
      T.reveal_type(other) # note: CaseNarrowingLocation
      0
    else
      T.reveal_type(other) # note: String
      other.length
    end
  end
end

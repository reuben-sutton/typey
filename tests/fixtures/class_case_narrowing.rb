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
      0
    else
      other.length
    end
  end
end

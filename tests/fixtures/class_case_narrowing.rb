# typed: strict

class CaseNarrowingLocation
  attr_reader :file

  #: (BasicObject other) -> Integer?
  def <=>(other)
    return unless CaseNarrowingLocation === other

    other.file
    0
  end
end

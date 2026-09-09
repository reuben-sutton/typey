# typed: true

class CfgClassPredicate
  attr_reader :file

  #: (BasicObject other) -> Integer?
  def <=>(other)
    return unless CfgClassPredicate === other

    other.file
    0
  end
end

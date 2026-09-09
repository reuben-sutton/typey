# typed: true

class LeftClassObject
  #: () -> String
  def self.value
    "left"
  end
end

class RightClassObject
  #: () -> Integer
  def self.value
    1
  end
end

scope = LeftClassObject #: as Class[T.any(LeftClassObject, RightClassObject)]
T.reveal_type(scope.value) # note: T.any(Integer, String)

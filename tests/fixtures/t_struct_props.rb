# typed: true

class Person < T::Struct
  prop :name, String
  prop :age, T.nilable(Integer)
end

person = Person.new(name: "Ada", age: nil)
T.reveal_type(person.name) # note: Revealed type: `String`
T.reveal_type(person.age) # note: Revealed type: `T.nilable(Integer)`
person.name = 1 # error: Expected `String`, but found `Integer`

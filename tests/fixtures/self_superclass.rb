# typed: true

class Parent
  def ping(value)
    value
  end

  class Child < self
    def run
      ping("ok")
    end
  end
end

T.reveal_type(Parent::Child.new.run) # note: String

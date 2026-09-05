# typed: true

class Greeting
  extend T::Sig

  sig { params(name: String).returns(String) }
  def self.render(name); end
end

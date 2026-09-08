# typed: true

class CfgDynamicMethod
  def self.install
    define_method(:value) do
      "ok".upcase
    end
  end
end

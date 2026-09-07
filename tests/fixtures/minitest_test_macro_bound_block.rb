# typed: true

module Minitest
  module Assertions
    def assert_equal(expected, actual)
      expected == actual
    end
  end

  class Test
    include Assertions

    class << self
      sig { params(name: String, "&": T.proc.bind(T.self_type).void).returns(NilClass) } # error: Unknown parameter name `&`
      def test(name, &block); end # error: Malformed `sig`. Type not specified for parameter `block`
    end
  end
end

class ExampleTest < Minitest::Test
  test "runs against an instance" do
    assert_equal 1, 1
  end
end

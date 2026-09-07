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
      # error: Malformed `sig`. Type not specified for parameter `block`
      # error: Unknown parameter name `&`
      sig { params(name: String, "&": T.proc.bind(T.self_type).void).returns(NilClass) }
      def test(name, &block); end
    end
  end
end

class ExampleTest < Minitest::Test
  test "runs against an instance" do
    assert_equal 1, 1
  end
end

# typed: true

module ActiveSupport
  module Testing
    module Declarative
      def test(name, &block)
      end
    end

    module SetupAndTeardown
      module ClassMethods
        def setup(*args, &block)
        end

        def teardown(*args, &block)
        end
      end
    end
  end

  class TestCase
    def assert_equal(expected, actual)
      expected == actual
    end
  end
end

ActiveSupport::TestCase.extend(ActiveSupport::Testing::Declarative)
ActiveSupport::TestCase.extend(ActiveSupport::Testing::SetupAndTeardown::ClassMethods)

class ExampleTest < ActiveSupport::TestCase
  test "runs against an instance" do
    assert_equal 1, 1
  end

  setup do
    assert_equal 1, 1
  end

  teardown do
    assert_equal 1, 1
  end
end

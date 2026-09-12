# typed: true

class TestSetupState
end

module Minitest
  class Test
    #: (TestSetupState) -> void
    def require_test_setup_state(value)
    end

    class << self
      def test(name, &block)
      end

      def setup(&block)
      end

      def teardown(&block)
      end
    end
  end
end

class BlockSetupTest < Minitest::Test
  setup do
    @direct_state = TestSetupState.new
    build_state
  end

  teardown do
    require_test_setup_state(@direct_state)
    require_test_setup_state(@helper_state)
  end

  test "setup state is available to tests" do
    require_test_setup_state(@direct_state)
    require_test_setup_state(@helper_state)
  end

  private

  def build_state
    @helper_state = TestSetupState.new
  end
end

class MethodSetupTest < Minitest::Test
  def setup
    @state = TestSetupState.new
  end

  test "method setup state is available to tests" do
    require_test_setup_state(@state)
  end
end

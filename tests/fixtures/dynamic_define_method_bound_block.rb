# typed: true

module TestAssertions
  def assert_equal(expected, actual)
    expected == actual
  end
end

module TestDsl
  def test(name, &block)
    define_method(name, &block)
  end
end

class TestBase
end

TestBase.include(TestAssertions)
TestBase.extend(TestDsl)

class ExampleTest < TestBase
  test "runs against an instance" do
    assert_equal 1, 1
  end
end

# typed: true

module TestAssertions
  def assert_equal(expected, actual)
    expected == actual
  end
end

module TestDsl
  sig { params(name: String, "&": T.proc.bind(T.self_type)).returns(NilClass) }
  def test(name, &block)
    nil
  end
end

class TestBase < Object
end

TestBase.include(TestAssertions)
TestBase.extend(TestDsl)

class ExampleTest < TestBase
  test "runs against an instance" do
    assert_equal 1, 1
  end
end

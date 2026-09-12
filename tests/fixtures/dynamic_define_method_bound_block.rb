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
    T.reveal_type(self) # note: Revealed type: `ExampleTest`
    assert_equal 1, 1
  end
end

class DynamicMethods
  def self.install
    define_method(:value) do |options|
      T.reveal_type(self) # note: Revealed type: `DynamicMethods`
      T.reveal_type(options) # note: Revealed type: `T.untyped`
      options.key?(:value)
    end
  end
end

DynamicMethods.install

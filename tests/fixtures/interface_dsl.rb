# typed: true

# @interface
# error: Classes can't be interfaces. Use `abstract!` instead of `interface!`
class InvalidInterface; end

module ValidInterface
  interface!
end

# typed: true

# @interface
class InvalidInterface; end # error: Classes can't be interfaces. Use `abstract!` instead of `interface!`

module ValidInterface
  interface!
end

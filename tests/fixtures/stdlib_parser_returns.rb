# typed: true

module Prism; end

T.reveal_type(Prism.parse("")) # note: Prism::ParseResult
T.reveal_type(Prism.parse_comments("")) # note: Prism::ParseResult
T.reveal_type(Prism.parse_file("test.rb")) # note: Prism::ParseResult

module RBS
  class Parser; end
end

T.reveal_type(RBS::Parser.parse_type("String")) # note: RBS::Types::Bases::Base
T.reveal_type(RBS::Parser.parse_method_type("() -> String")) # note: RBS::MethodType
T.reveal_type(RBS::Parser.parse_type_params("[A]")) # note: T::Array[RBS::AST::TypeParam]
T.reveal_type(RBS::Parser.parse_signature("class Foo; end")) # note: [RBS::Buffer, T::Array[RBS::AST::Directives::Base], T::Array[RBS::AST::Declarations::Base]]

# typed: true

module Prism; end

T.reveal_type(Prism.parse("")) # note: Prism::ParseResult
T.reveal_type(Prism.parse_comments("")) # note: Prism::ParseResult
T.reveal_type(Prism.parse_file("test.rb")) # note: Prism::ParseResult

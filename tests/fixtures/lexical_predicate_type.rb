# typed: strict

class Error
  attr_reader :message
end

module LexicalPredicate
  class Error
    attr_reader :message

    #: (BasicObject other) -> String?
    def message_from(other)
      return unless other.is_a?(Error)

      other.message
    end

    #: (BasicObject other) -> String?
    def cast_message(other)
      T.cast(other, Error).message
    end
  end
end

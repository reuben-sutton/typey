# typed: true

module StateStore
  extend T::Sig

  sig { params(key: Symbol).returns(T::Hash[Symbol, String]) }
  def self.[](key)
    { key => "value" }
  end

  sig { params(key: Symbol, value: T::Hash[Symbol, String]).returns(T::Hash[Symbol, String]) }
  def self.[]=(key, value)
    value
  end
end

registry = StateStore[:key] ||= {}
T.reveal_type(registry[:key]) # note: String

module ActiveSupport
  module NestedStateStore
    extend T::Sig

    sig { params(key: Symbol).returns(String) }
    def self.[](key)
      key.to_s
    end
  end
end

T.reveal_type(ActiveSupport::NestedStateStore[:key]) # note: String

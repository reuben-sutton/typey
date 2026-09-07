# typed: true

module SelfExtended
  extend self

  def value
    "value"
  end
end

T.reveal_type(SelfExtended.value) # note: String

module IncludedSelfMethods
  def dump
    "dump"
  end
end

module SelfExtendedWithInclude
  include IncludedSelfMethods
  extend self
end

T.reveal_type(SelfExtendedWithInclude.dump) # note: String

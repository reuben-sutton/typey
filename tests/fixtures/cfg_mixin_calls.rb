# typed: true

module IncludedMethods
  def included_value
    "included"
  end
end

module PrependedMethods
  def prepended_value
    1
  end
end

module ExtendedMethods
  def extended_value
    :extended
  end
end

class IncludedHost
  include IncludedMethods
end

class PrependedHost
  prepend PrependedMethods
end

class ExtendedHost
  extend ExtendedMethods
end

T.reveal_type(IncludedHost.new.included_value) # note: String
T.reveal_type(PrependedHost.new.prepended_value) # note: Integer
T.reveal_type(ExtendedHost.extended_value) # note: Symbol

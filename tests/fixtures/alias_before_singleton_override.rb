# typed: true

class AliasBeforeSingletonOverride
  def initialize(*args)
  end

  class << self
    alias_method :create, :new

    def new(name)
      name
    end
  end
end

T.reveal_type(AliasBeforeSingletonOverride.create("zone", nil, nil)) # note: AliasBeforeSingletonOverride

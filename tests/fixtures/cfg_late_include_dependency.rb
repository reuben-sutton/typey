# typed: true

module LaterMethods
  def later_value
    1
  end
end

class LateBase
  def use_later_method
    later_value
  end
end

class LateChild < LateBase
end

class LateInstaller
  def self.install(base)
    base.include(LaterMethods)
  end
end

LateInstaller.install(LateChild)
T.reveal_type(LateChild.new.use_later_method) # note: Revealed type: `Integer`

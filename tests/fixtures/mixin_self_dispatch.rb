# typed: true

module PathMethods
  def path
    root
  end
end

class Host
  include PathMethods

  sig { returns(String) }
  def root
    "root"
  end
end

T.reveal_type(Host.new.path) # note: String

# typed: true

module Root
  class Snapshot
    #: String
    attr_accessor :commit_sha
  end
end

value = Root::Snapshot.new.commit_sha
T.reveal_type(value) # note: String

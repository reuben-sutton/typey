# typed: true

class Commit
  #: -> Time
  def time
    Time.now
  end
end

class Timeline
  #: (Time) -> void
  def initialize(from)
  end
end

class Runner
  #: -> Commit?
  def sorbet_intro_commit
    nil
  end

  #: (String?) -> Time?
  def parse_time(value)
    return unless value

    Time.now
  end

  #: (String?) -> void
  def run(value)
    from = parse_time(value)
    to = parse_time(value)
    unless from
      commit = sorbet_intro_commit
      commit = T.must(commit)
      from = commit.time
    end
    Timeline.new(from)
    Timeline.new(to) # error: Expected `Time`, but found `T.nilable(Time)`
  end
end

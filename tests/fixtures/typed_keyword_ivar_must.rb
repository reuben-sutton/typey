# typed: true

class Report
  #: (snapshots: Array[String]) -> void
  def initialize(snapshots:)
    @snapshots = snapshots
  end

  #: -> String
  def last_snapshot
    T.must(@snapshots.last)
  end
end

T.reveal_type(Report.new(snapshots: ["latest"]).last_snapshot) # note: String

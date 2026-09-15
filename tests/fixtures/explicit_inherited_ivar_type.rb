# typed: true

class ProjectContract
  #: -> String
  def work
    "done"
  end
end

class ParentContract
  #: ProjectContract
  attr_reader :project
end

class ChildContract < ParentContract
  #: -> String
  def run
    @project.work
  end
end

T.reveal_type(ChildContract.new.run) # note: Revealed type: String

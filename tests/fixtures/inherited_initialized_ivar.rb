# typed: true

class Project
  #: -> String
  def work
    "done"
  end
end

class Parent
  #: Project
  attr_reader :project

  #: -> void
  def initialize
    @project = Project.new
  end
end

class Child < Parent
  #: -> void
  def setup
    T.reveal_type(@project) # note: Revealed type: Project
    @project.work
  end
end

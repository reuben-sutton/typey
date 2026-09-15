# typed: true

module Outer
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

  module Inner
    class Child < Parent
      #: -> String
      def run
        @project.work
      end
    end
  end
end

T.reveal_type(Outer::Inner::Child.new.run) # note: Revealed type: String

# typed: true

class CfgFileSet
  #: () -> void
  def initialize
    @files = nil #: Array[String]?
  end

  #: -> Array[String]
  def files
    @files ||= files_for_processing
  end

  #: -> Array[String]
  def files_for_processing
    ["file"]
  end
end

class CfgBaseCommand
  #: () -> void
  def initialize
  end
end

# @requires_ancestor: CfgBaseCommand
module CfgUsesFileSet
  #: () -> void
  def initialize
    super
    @files_for_processing = fetch_files_to_process #: CfgFileSet
  end

  #: -> CfgFileSet
  def fetch_files_to_process
    CfgFileSet.new
  end
end

class CfgCommand < CfgBaseCommand
  include CfgUsesFileSet

  #: -> bool
  def run
    @files_for_processing.files.empty?
  end
end

T.reveal_type(CfgCommand.new.run) # note: T::Boolean

# typed: true

module Minitest
  class Runnable
    def name
      "name"
    end
  end
end

module RunnableHelper
  def helper_name
    #: self as Minitest::Runnable
    name
  end
end

module AST
  class Node
    def children
      "children"
    end
  end
end

module Parser
  module AST
    class Node < ::AST::Node
    end
  end
end

sig { params(node: Parser::AST::Node).returns(String) }
def inherited_children(node)
  node.children
end

sig { params(parts: T::Array[String]).returns(String) }
def join_parts(parts)
  File.join(*parts)
end

sig { params(path: String).returns(String) }
def join_string_path(path)
  File.join(*path)
end

sig { params(command: T.any(String, T::Array[String])).returns(T::Array[String]) }
def normalize_command(command)
  Array(command)
end

sig { params(files: T::Set[String]).void }
def accept_files(files)
end

accept_files(Set[])

ENV["TYPEY_TEST"] = "value"

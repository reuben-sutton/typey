# typed: true

class CfgHashLiteralKeys
  #: -> bool
  def relative_paths_empty?
    options = {
      relative_file_paths: [], #: Array[String]
      ignore_nested_packages: false, #: bool
      formatter_name: nil, #: String?
    }
    options[:relative_file_paths].empty?
  end

  #: -> String?
  def formatter_name # error: Expected method `formatter_name` to return
    options = {
      relative_file_paths: [], #: Array[String]
      formatter_name: nil, #: String?
    }
    options[:formatter_name]
  end

  #: -> Integer
  def updated_value # error: Expected method `updated_value` to return
    options = {
      name: "value",
      other: false,
    }
    options[:name] = 1 # error: Expected `T.any(FalseClass, String)`, but found `Integer`
    options[:name]
  end
end

T.reveal_type(CfgHashLiteralKeys.new.relative_paths_empty?) # note: T::Boolean
T.reveal_type(CfgHashLiteralKeys.new.formatter_name) # note: T.nilable(String)
T.reveal_type(CfgHashLiteralKeys.new.updated_value) # note: Integer

class CfgIvarHashLiteralKeys
  #: -> Array[String]
  def relative_file_paths # error: Expected method `relative_file_paths` to return
    @options = {
      relative_file_paths: [], #: Array[String]
      ignore_nested_packages: false, #: bool
    }
    @options[:relative_file_paths]
  end
end

T.reveal_type(CfgIvarHashLiteralKeys.new.relative_file_paths) # note: T::Array[String]

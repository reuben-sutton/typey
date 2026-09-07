# typed: true

class AliasMethodStringNames
  def value
    1
  end

  # Ruby accepts strings as well as symbols for both names.
  alias_method "renamed", "value"
end

T.reveal_type(AliasMethodStringNames.new.renamed) # note: Integer

class Module
  def self.attr_internal_naming_format
    "_%s"
  end

  def alias_string_names
    name = "value"
    alias_method name, name
  end

  def attr_internal_define(attr_name, type)
    internal_name = Module.attr_internal_naming_format % attr_name
    public_send("attr_#{type}", internal_name)
    attr_name, internal_name = "#{attr_name}=", "#{internal_name}=" if type == :writer
    alias_method attr_name, internal_name
    remove_method internal_name
  end
end

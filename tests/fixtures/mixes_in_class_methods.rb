# typed: true

module ExtensionMethods
  def class_api
    "ok"
  end
end

module Extension
  mixes_in_class_methods ExtensionMethods
end

class Host
  include Extension
end

Host.class_api

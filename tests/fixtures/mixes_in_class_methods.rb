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

T.reveal_type(Host.class_api) # note: Revealed type: `String`

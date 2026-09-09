# typed: true

module CfgDynamicStruct
  Reference = Struct.new(:name, keyword_init: true)

  def self.build
    Reference.new(name: "ready")
  end
end

value = CfgDynamicStruct.build
T.reveal_type(value.name) # note: String

# typed: true

module CfgStructAlias
  Reference = Struct.new(:name, keyword_init: true)

  #: (String name) -> Reference
  def self.build(name)
    Reference.new(name: name)
  end
end

T.reveal_type(CfgStructAlias.build("ready")) # note: Reference

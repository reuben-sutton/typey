# typed: true

module CfgRuntimeConstantIndexer
  def self.[](value)
    value.to_s
  end
end

T.reveal_type(CfgRuntimeConstantIndexer[:key]) # note: String

# typed: true
# conformance: cfg

class CfgOptionalDefaultFlow < Hash
  def initialize(parent = nil)
    @parent = parent
    if @parent.kind_of?(CfgOptionalDefaultFlow)
      super() { |_hash, _key| nil }
    elsif @parent
      super() { |_hash, _key| nil }
    else
      super()
      @parent = {}
    end
  end

  def self.convert(value, conversion: nil)
    if value.is_a?(Array)
      value.each { |entry| convert(entry, conversion: conversion) }
    end
    value
  end
end

CfgOptionalDefaultFlow.new(CfgOptionalDefaultFlow.new)
CfgOptionalDefaultFlow.new({})
CfgOptionalDefaultFlow.new
CfgOptionalDefaultFlow.convert([], conversion: :assignment)

T.reveal_type(CfgOptionalDefaultFlow.new) # note: CfgOptionalDefaultFlow

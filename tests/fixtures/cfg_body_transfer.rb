class CfgBodyTransfer
  def value
    local = 1
    @value = local
    @value.to_s
  end
end

CfgBodyTransfer.new.value

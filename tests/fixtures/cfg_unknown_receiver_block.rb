# typed: true

def each_unknown(values)
  values.each do |value|
    value.to_s
  end
end

class ConcreteNoBlockContract
  def call
    nil
  end
end

def each_on_concrete_method_without_block_contract
  ConcreteNoBlockContract.new.call do
    "value".upcase
  end
end

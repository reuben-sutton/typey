# typed: true
# conformance: cfg

extend T::Sig

def terminate_with_callback(&block)
  block.call
end

def invoke_callback(&block)
  block.call
end

sig { params(value: String).void }
def needs_string(value); end

def sample
  terminate_with_callback do
    return
  end

  invoke_callback do
    needs_string(1) # error: Expected `String`, but found `Integer`
  end
end

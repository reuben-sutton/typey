# typed: true
# conformance: cfg

def cfg_until_loop_flow
  stop = false
  Thread.new do
    until stop
      stop.to_s
    end
  end
  stop = true
end

cfg_until_loop_flow

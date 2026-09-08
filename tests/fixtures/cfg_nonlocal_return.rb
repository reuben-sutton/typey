def invoke
  yield
end

def returns_from_block
  invoke do
    return "from block"
  end

end

def returns_with_ensure
  begin
    return "from ensure"
  ensure
    @touched = true
  end
end

T.reveal_type(returns_from_block) # note: String
T.reveal_type(returns_with_ensure) # note: String

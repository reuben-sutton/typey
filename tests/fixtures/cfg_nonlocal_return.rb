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

def returns_after_break(flag)
  invoke do
    break if flag

    return "from block"
  end

  "continued"
end

def returns_after_next(flag)
  invoke do
    next if flag

    return "from block"
  end

  "continued"
end

T.reveal_type(returns_from_block) # note: String
T.reveal_type(returns_with_ensure) # note: String
T.reveal_type(returns_after_break(true)) # note: String
T.reveal_type(returns_after_next(true)) # note: String

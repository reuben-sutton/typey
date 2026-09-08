class CfgLoopBody
  #: (Integer) -> Integer
  def increment_to(limit)
    current = 0
    while current < limit
      current = current + 1
    end
    current
  end

  #: (Integer) -> Integer
  def stop_at_two(limit)
    current = 0
    while current < limit
      break if current == 2
      current = current + 1
    end
    current
  end

  #: (Integer) -> Integer
  def skip_first(limit)
    current = 0
    while current < limit
      current = current + 1
      next if current == 1
      current = current + 1
    end
    current
  end
end

T.reveal_type(CfgLoopBody.new.increment_to(3)) # note: Revealed type: `Integer`
T.reveal_type(CfgLoopBody.new.stop_at_two(5)) # note: Revealed type: `Integer`
T.reveal_type(CfgLoopBody.new.skip_first(5)) # note: Revealed type: `Integer`

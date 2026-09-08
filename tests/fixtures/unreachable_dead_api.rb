# typed: true

def unreachable_dead_api
  return 1
  missing_method # error: This expression appears after an unconditional return
end

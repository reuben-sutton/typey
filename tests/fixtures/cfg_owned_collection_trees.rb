# typed: true

integers = [1, 2]
nested = [[3], [4]]
combined = [*integers, *nested]
properties = {integers: integers, **{nested: nested}}

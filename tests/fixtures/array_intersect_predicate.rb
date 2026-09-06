# typed: true

paths = ["lib"]
T.reveal_type(paths.intersect?(["lib"])) # note: T::Boolean

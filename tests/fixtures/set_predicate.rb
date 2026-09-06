# typed: true

constants = ["MSG", "RESTRICT_ON_SEND"].to_set
T.reveal_type(constants.include?("MSG")) # note: T::Boolean

T.reveal_type(Time.local(1, 0, 0, 1, 1, 2024, nil, nil, false, nil)) # note: Revealed type: `Time`
T.reveal_type(Time.at(1, 2, :nanosecond, in: "UTC")) # note: Revealed type: `Time`

# typed: true

Signal.trap("INT") { abort "interrupted" }
T.reveal_type("after signal".upcase) # note: Revealed type: `String`

Thread.new { abort "in thread" }
T.reveal_type(1 + 1) # note: Revealed type: `Integer`

# typed: true

T.reveal_type(1.class) # note: Revealed type: `Class[Integer]`
T.reveal_type("text".class) # note: Revealed type: `Class[String]`
T.reveal_type([1].class) # note: Revealed type: `Class[Array]`

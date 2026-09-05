# typed: true

formatted = format_name(1)
rendered = Greeting.render("world")

T.reveal_type(formatted) # note: String
T.reveal_type(rendered) # note: String

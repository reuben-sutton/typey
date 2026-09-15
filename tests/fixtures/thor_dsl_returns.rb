# typed: true

class Thor; end

class Command < Thor
  T.reveal_type(default_task(:run)) # note: String
  T.reveal_type(desc("run", "Run the command")) # note: FalseClass
  T.reveal_type(option(:verbose, type: :boolean)) # note: Thor::Option
end

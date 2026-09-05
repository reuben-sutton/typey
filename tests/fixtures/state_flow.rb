Answer = 41

module Config
  VALUE = "configured"
  @@shared = VALUE

  def shared
    @@shared
  end
end

class ConfigConsumer
  include Config

  def value
    Config::VALUE
  end
end

class BaseCounter
  @@count = 0
end

class Counter < BaseCounter
  def count
    @@count
  end
end

$global = Answer

def read_global
  $global
end

T.reveal_type(Answer) # note: Integer
T.reveal_type(Config::VALUE) # note: String
T.reveal_type(ConfigConsumer.new.shared) # note: String
T.reveal_type(ConfigConsumer.new.value) # note: String
T.reveal_type(Counter.new.count) # note: Integer
T.reveal_type($global) # note: Integer
T.reveal_type(read_global) # note: Integer

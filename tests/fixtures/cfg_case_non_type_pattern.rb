# typed: true

def choose_parser(path)
  case path
  when /\.rb\z/
    "ruby".upcase
  else
    "other".upcase
  end
end

# typed: true

class NonemptyStringBlockIndex
  #: -> String
  def nested_string
    "thing_name".to_s.gsub(/(?:^|_)([a-z\d]*)/i) do |match|
      match = match.delete_prefix("_")
      !match.empty? ? T.reveal_type(match[0]) : +"" # note: String
    end
  end

  #: (String) -> String
  def convert(value)
    value = value.delete_prefix("_")
    !value.empty? ? T.reveal_type(value[0]) : +"" # note: String
  end

  #: (String) -> String
  def gsub_convert(value)
    value.gsub(/x/) do |match|
      match = match.delete_prefix("_")
      !match.empty? ? T.reveal_type(match[0]) : +"" # note: String
    end
  end
end

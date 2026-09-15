# typed: true

class Object
  def to_query(key)
    "#{key}"
  end
end

[1].to_query("key")
{}.to_query("key")
T.reveal_type([1].to_query("key")) # note: String

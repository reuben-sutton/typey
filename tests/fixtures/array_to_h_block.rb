# typed: true

class Entry
  #: -> String
  def key
    "entry"
  end
end

entries = [Entry.new]
T.reveal_type(entries.to_h { |entry| [entry.key, entry] }) # note: T::Hash[String, Entry]

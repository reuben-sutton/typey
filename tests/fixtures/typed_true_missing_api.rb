# typed: true

class MissingApiReceiver
  def known
    "known"
  end

  def call_missing_implicitly
    definitely_missing # error: Method `definitely_missing` does not exist on `MissingApiReceiver`
  end
end

receiver = MissingApiReceiver.new
receiver.missing # error: Method `missing` does not exist on `MissingApiReceiver`
T.reveal_type(receiver.known) # note: String
receiver.call_missing_implicitly
"value".missing # error: Method `missing` does not exist on `String`

# typed: true

class MissingApiReceiver
  def known
    "known"
  end

  def call_missing_implicitly
    definitely_missing
  end
end

receiver = MissingApiReceiver.new
receiver.missing # error: Method `missing` does not exist on `MissingApiReceiver`
receiver.known
receiver.call_missing_implicitly # error: Method `definitely_missing` does not exist on `MissingApiReceiver`
"value".missing # error: Method `missing` does not exist on `String`

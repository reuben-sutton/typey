# typed: true

# This unrelated alias must not change the meaning of Process::Status.
#: type status = Symbol

require "open3"

out, status = Open3.capture2e("echo")
T.reveal_type(out) # note: String
T.reveal_type(status) # note: Process::Status
status.success?
T.reveal_type(status.exitstatus) # note: T.nilable(Integer)

opts = {chdir: "."}
out, status = Open3.capture2e("echo", opts)
T.reveal_type(status) # note: Process::Status
status.success?

def run_capture(path)
  opts = {}
  opts[:chdir] = path
  out, status = Open3.capture2e("bundle install", opts)
  T.reveal_type(status) # note: Process::Status
  status.success?
end

class Holder
  def self.no_commands(&)
  end

  no_commands do
    def nested_capture(path)
      opts = {}
      opts[:chdir] = path
      out, status = Open3.capture2e("bundle install", opts)
      T.reveal_type(status) # note: Process::Status
      status.success?
    end
  end
end

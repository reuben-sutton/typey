# typed: true

files = Dir.glob("*.rb")
T.reveal_type(files) # note: Revealed type: `T::Array[String]`
T.reveal_type(Dir.glob("*.rb") { |path| path }) # note: Revealed type: `NilClass`

file = File.open("output.txt", "w")
T.reveal_type(file) # note: Revealed type: `File`
file.close
T.reveal_type(File.open("output.txt", "w") { |handle| handle }) # note: Revealed type: `File`

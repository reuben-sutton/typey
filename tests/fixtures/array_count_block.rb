# typed: true

values = ["path.rb"] #: Array[String]
values.count { |file| T.reveal_type(file.end_with?(".rb")) }

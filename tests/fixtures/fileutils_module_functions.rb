# typed: true

T.reveal_type(FileUtils.rm_rf("tmp")) # note: NilClass
T.reveal_type(FileUtils.mkdir_p("tmp")) # note: T::Array[String]

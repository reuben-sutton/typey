# typed: true

module Enumerable
  def cfg_implicit_global_blocks
    each { "implicit each".upcase }
    to_enum(:each) { "implicit enum".upcase }
  end
end

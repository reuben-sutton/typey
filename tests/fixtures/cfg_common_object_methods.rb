# typed: true

class CfgCommonObjectMethods
  #: () -> String
  def self.method
    "declared"
  end
end

T.reveal_type(CfgCommonObjectMethods.name) # note: T.nilable(String)
T.reveal_type(CfgCommonObjectMethods.new.dup) # note: CfgCommonObjectMethods
T.reveal_type(CfgCommonObjectMethods.new.freeze) # note: CfgCommonObjectMethods
T.reveal_type(CfgCommonObjectMethods.new.to_s) # note: String
T.reveal_type(CfgCommonObjectMethods.new.nil?) # note: T::Boolean
T.reveal_type(CfgCommonObjectMethods.new.method(:to_s)) # note: Method
T.reveal_type(CfgCommonObjectMethods.method) # note: String

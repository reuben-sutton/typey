# typed: true

class SingletonClassAccessorContract
  @value = "initial"
  singleton_class.attr_accessor :value
end

T.reveal_type(SingletonClassAccessorContract.value) # note: String
SingletonClassAccessorContract.value = "updated"

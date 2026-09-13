# typed: true

module PrependedKernelMethods
  def run
    catch(:tag) { eval("1") }
  end
end

class PrependedKernelHost
  prepend PrependedKernelMethods
end

class AnotherPrependedKernelHost
  prepend PrependedKernelMethods
end

T.reveal_type(PrependedKernelHost.new.run) # note: T.untyped

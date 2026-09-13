module IncludedConstants
  VALUE = "from an included module"
end

class IncludedConstantUser
  include IncludedConstants
end

T.reveal_type(IncludedConstantUser::VALUE) # note: Revealed type: `String`

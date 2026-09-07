# typed: true

extend T::Sig

sig { params("&": T.proc.void).returns(NilClass) } # error: Unknown parameter name `&`
def register(&block); end # error: Malformed `sig`. Type not specified for parameter `block`

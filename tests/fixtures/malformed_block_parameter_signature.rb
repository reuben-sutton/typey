# typed: true

extend T::Sig

# error: Unknown parameter name `&`
# error: Malformed `sig`. Type not specified for parameter `block`
sig { params("&": T.proc.void).returns(NilClass) }
def register(&block); end

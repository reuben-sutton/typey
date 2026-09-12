# typed: true

def validate_names(*names)
  names.each do |name|
    unless name.is_a?(Symbol) || name.is_a?(String)
      raise TypeError
    end

    T.reveal_type(name) # note: Revealed type: `Symbol`
    name
  end
end

T.reveal_type(validate_names(:name)) # note: Revealed type: `T::Array[Symbol]`

# typed: true

def validate_names(*names)
  names.each do |name|
    unless name.is_a?(Symbol) || name.is_a?(String)
      raise TypeError
    end

    name
  end
end

validate_names(:name)

# typed: true

def scan(values)
  skipped = false
  values.each do |location|
    unless skipped
      skipped = true
      next
    end

    frame = location if location
    return frame if frame
  end
end

scan([nil, "frame"])

def sole(values)
  found = false
  values.each do |value|
    raise "too many" if found

    found = true
    value
  end
end

sole([1, 2])

# typed: true

def build_strings
  values = []
  values << "value"
  values
end

def build_pair
  class_methods, methods = [], []
  class_methods << "method"
  methods << "other"
  [class_methods, methods]
end

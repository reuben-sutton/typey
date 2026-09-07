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

def build_modifiers(flag)
  modifiers = []
  modifiers << :nx if flag
  modifiers << :px << (1000 * 1)
  modifiers
end

def build_expiry_modifiers(unless_exist = false, expires_in = nil)
  modifiers = []
  if unless_exist || expires_in
    modifiers << :nx if unless_exist
    modifiers << (1000 * expires_in.to_f).ceil if expires_in
  end
  modifiers
end

build_expiry_modifiers(true, nil)
build_expiry_modifiers(false, 1)

# typed: true

def build_strings
  values = []
  values << "value"
  T.reveal_type(values) # note: T::Array[String]
  values
end

def build_pair
  class_methods, methods = [], []
  class_methods << "method"
  methods << "other"
  T.reveal_type(class_methods) # note: T::Array[String]
  T.reveal_type(methods) # note: T::Array[String]
  [class_methods, methods]
end

def build_modifiers(flag)
  modifiers = []
  modifiers << :nx if flag
  modifiers << :px << (1000 * 1)
  T.reveal_type(modifiers) # note: T::Array[T.any(Integer, Symbol)]
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

# typed: true

class Class
  def class_attribute(*)
  end
end

class Settings
  class_attribute :enabled
end

class SettingsChild < Settings
  def read
    enabled
  end
end

T.reveal_type(Settings.enabled) # note: T.untyped
T.reveal_type(Settings.new.enabled) # note: T.untyped
T.reveal_type(Settings.enabled?) # note: T::Boolean
T.reveal_type(Settings.new.enabled?) # note: T::Boolean

class RestrictedSettings
  class_attribute :value, instance_accessor: false, instance_predicate: false
end

T.reveal_type(RestrictedSettings.value) # note: T.untyped
RestrictedSettings.new.value # error: Method `value` does not exist on `RestrictedSettings`

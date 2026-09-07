# typed: true

def after_nonempty_array_guard
  values = [1]
  return if values.empty?

  "after"
end

def after_array_union_guard
  values = ["one"] | ["two"]
  T.reveal_type(values) # note: T::Array[String]
  return if values.empty?

  values.first
end

module Gem
  def self.path
    ["/gems"]
  end

  def self.default_dir
    "/default"
  end
end

def after_gem_path_guard
  gems_paths = (Gem.path | [Gem.default_dir]).map { |path| path }
  return if gems_paths.empty?

  gems_paths.first
end

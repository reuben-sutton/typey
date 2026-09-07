# typed: true

T.reveal_type(Gem.path) # note: T.untyped

def gem_paths
  paths = (Gem.path | [Gem.default_dir]).map { |path| path }
  return if paths.empty?

  paths.first
end

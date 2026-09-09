# typed: true

class CacheResult
end

class Cache
  sig { params(path: String, block: T.proc.returns(T::Array[String])).returns(T::Array[String]) }
  def with_cache(path, &block)
    yield
  end
end

sig { params(cache: Cache, node: T.nilable(String)).returns(T.any(CacheResult, T::Array[String])) }
def process_cache(cache, node)
  references = cache.with_cache("cache") do
    return CacheResult.new unless node

    ["reference"]
  end

  references
end

T.reveal_type(process_cache(Cache.new, "node")) # note: `T.any(CacheResult, T::Array[String])`

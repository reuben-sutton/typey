# typed: true

module Rails
  class Application
    def routes
    end
  end

  class << self
    def application
    end
  end
end

module ActionDispatch
  module Routing
    class RouteSet
      def draw(&block)
      end
    end

    class Mapper
      def root(path)
      end

      def route_only
        "route"
      end
    end
  end
end

class RailsSorbetApplication < Rails::Application
end

Rails.application.routes.draw do
  root "posts#index"
  route_only
end

T.reveal_type(Rails.application.routes) # note: Revealed type: `ActionDispatch::Routing::RouteSet`

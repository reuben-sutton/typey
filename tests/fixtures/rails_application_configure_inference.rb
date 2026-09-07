# typed: true

module Rails
  class Application
    def configure(&block)
    end

    def application_only
      "application"
    end
  end

  class << self
    def application
    end
  end
end

class RailsSorbetApplication < Rails::Application
end

Rails.application.configure do
  application_only
end

T.reveal_type(Rails.application) # note: Revealed type: `RailsSorbetApplication`

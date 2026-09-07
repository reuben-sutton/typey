# typed: true

module GeneratedBuilderMethods
  attr_reader :generator
  attr_reader :options

  class_eval do
    def template(path)
      generator.template(path)
    end

    def configured_path
      options.key?(:path) ? "configured" : "default"
    end
  end
end

class TemplateGenerator
  def template(path)
    "template:#{path}"
  end
end

class DynamicBuilder
  def initialize(generator, options)
    @generator = generator
    @options = options
  end

  def uses_mixed_in_options
    options.key?(:path) ? "configured" : "default"
  end
end

class CustomBuilder < DynamicBuilder
end

class BuilderFactoryBase
  def install
    builder_class = get_builder_class
    builder_class.include(GeneratedBuilderMethods)
  end

  def build
    install
    builder_class = get_builder_class
    builder = builder_class.new(TemplateGenerator.new, { path: "Gemfile" })
    [builder.template("Gemfile"), builder.configured_path, builder.uses_mixed_in_options]
  end
end

class BuilderFactory < BuilderFactoryBase
  def get_builder_class
    defined?(::CustomBuilder) ? ::CustomBuilder : DynamicBuilder
  end
end

T.reveal_type(BuilderFactory.new.build) # note: Revealed type: `T::Array[String]`

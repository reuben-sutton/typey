use std::path::Path;

use typey::diagnostic::Severity;
use typey::{check, CheckerConfig, Type, TypeLattice};

fn expected_errors(source: &str) -> Vec<&str> {
    source
        .lines()
        .filter_map(|line| {
            line.split_once("# error:")
                .map(|(_, message)| message.trim())
        })
        .collect()
}

fn check_fixture(path: &str) -> typey::CheckResult {
    let source = std::fs::read_to_string(Path::new(path)).expect("fixture exists");
    let result = check(&source, CheckerConfig::default());
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    let expected = expected_errors(&source);
    assert_eq!(
        errors.len(),
        expected.len(),
        "unexpected diagnostics for {path}: {:?}",
        result.diagnostics
    );
    for message in expected {
        assert!(
            errors
                .iter()
                .any(|diagnostic| diagnostic.message.contains(message)),
            "fixture {path} did not contain `{message}`: {:?}",
            result.diagnostics
        );
    }
    result
}

fn assert_no_errors(source: &str) {
    let result = check(source, CheckerConfig::default());
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    assert!(errors.is_empty(), "unexpected diagnostics: {errors:?}");
}

#[test]
fn ignores_typed_ignore_files_before_parsing() {
    let result = check(
        "# typed: ignore\ndef broken(\n  this is not valid Ruby\n",
        CheckerConfig::default(),
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.types.is_empty(), "{:?}", result.types);
}

#[test]
fn checks_rbs_comments_and_trailing_assertions() {
    let result = check_fixture("tests/fixtures/rbs_comments.rb");
    assert!(result.diagnostics.iter().any(|diagnostic| diagnostic
        .message
        .contains("Revealed type: `T::Array[Integer]`")));
}

#[test]
fn checks_sorbet_sig_calls() {
    check_fixture("tests/fixtures/sorbet_sig.rb");
}

#[test]
fn checks_splat_call_shapes() {
    check_fixture("tests/fixtures/splat_comparison.rb");
}

#[test]
fn resolves_method_summaries_across_fixpoint_rounds() {
    let result = check_fixture("tests/fixtures/fixpoint_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("T.any(Integer, String)"))
            .count(),
        2,
        "{notes:?}"
    );
}

#[test]
fn joins_conditional_method_definitions_instead_of_overwriting() {
    let result = check(
        r#"
if RUBY_VERSION >= "4.0"
  def versioned_value
    1
  end
else
  def versioned_value
    "legacy"
  end
end

T.reveal_type(versioned_value)
"#,
        CheckerConfig::default(),
    );
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("T.any(Integer, String)")),
        "{notes:?}"
    );
}

#[test]
fn resolves_receiver_methods_ivars_and_control_flow() {
    let result = check_fixture("tests/fixtures/spinel_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `Integer`",
        "Revealed type: `String`",
        "Revealed type: `T.any(Float, Integer, NilClass)`",
        "Revealed type: `T.any(Integer, NilClass, String)`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T.nilable(String)`",
        "Revealed type: `T::Array[String]`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn resolves_mixins_aliases_and_super() {
    let result = check_fixture("tests/fixtures/dispatch_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        4,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Symbol`"))
            .count(),
        1,
        "{notes:?}"
    );
}

#[test]
fn handles_ruby_forwarding_and_zsuper() {
    assert_no_errors(
        r#"
def target(value)
  value
end

def wrapper(...)
  target(...)
end

class Parent
  def call(value)
    value
  end
end

class Child < Parent
  def call(...)
    super
  end
end

wrapper(1)
Child.new.call(2)
"#,
    );
}

#[test]
fn substitutes_self_type_and_builtin_exception_subtypes() {
    assert_no_errors(
        r#"
class Box
  sig { returns(T.nilable(T.self_type)) }
  def presence
    self if true
  end
end

class Reporter
  sig { params(error: Exception).void }
  def report(error); end

  sig { params(error: T.any(Exception, String)).void }
  def unexpected(error)
    error = RuntimeError.new(error) if error.is_a?(String)
    report(error)
  end
end
"#,
    );
}

#[test]
fn binds_rescue_splats_to_exception_instances() {
    assert_no_errors(
        r#"
class Reporter
  sig { params(error: Exception).void }
  def report(error); end

  sig { params(error_classes: T.class_of(Exception)).void }
  def handle(*error_classes)
    begin
      raise "boom"
    rescue *error_classes => error
      report(error)
    end
  end
end
"#,
    );
}

#[test]
fn evaluates_implicit_enumerable_blocks_for_flow() {
    assert_no_errors(
        r#"
module Enumerable
  sig { returns(Elem) }
  def sole
    result = nil
    found = false

    each do |*element|
      result = element.size == 1 ? element[0] : element
      found = true
    end

    if found
      result
    else
      raise "no item found"
    end
  end
end
"#,
    );
}

#[test]
fn refines_pattern_matches_and_exception_edges() {
    let result = check_fixture("tests/fixtures/pattern_exception_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `Integer`",
        "Revealed type: `T.nilable(String)`",
        "Revealed type: `String`",
        "Revealed type: `Integer`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        2,
        "{notes:?}"
    );
}

#[test]
fn tracks_constants_class_variables_and_globals() {
    let result = check_fixture("tests/fixtures/state_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        3,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        4,
        "{notes:?}"
    );
}

#[test]
fn resolves_extended_and_singleton_class_methods() {
    let result = check_fixture("tests/fixtures/singleton_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Symbol`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
}

#[test]
fn carries_proc_results_through_calls() {
    let result = check_fixture("tests/fixtures/closure_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Symbol`")),
        "{notes:?}"
    );
}

#[test]
fn carries_explicit_flow_outcomes_through_loops_and_rescues() {
    let result = check_fixture("tests/fixtures/flow_outcomes.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `String`",
        "Revealed type: `T.nilable(String)`",
        "Revealed type: `NilClass`",
        "Revealed type: `Symbol`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        3,
        "{notes:?}"
    );
}

#[test]
fn refines_locals_with_meet_and_joins_paths() {
    let result = check_fixture("tests/fixtures/lattice_flow.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `NilClass`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[T.any(Float, Integer)]`")),
        "{notes:?}"
    );
}

#[test]
fn prism_parse_is_the_only_parser_entrypoint() {
    let parsed = typey::prism::parse(b"answer = 42\n");
    assert_eq!(parsed.errors().count(), 0);
    assert_eq!(
        typey::prism::text(b"answer = 42\n", &parsed.node()),
        "answer = 42"
    );
}

#[test]
fn lattice_facade_has_top_and_bottom_identities() {
    let lattice = TypeLattice;
    assert_eq!(lattice.join(&Type::bottom(), &Type::Integer), Type::Integer);
    assert_eq!(lattice.meet(&Type::top(), &Type::Integer), Type::Integer);
    assert_eq!(
        Type::Integer.join(&Type::named("Numeric")),
        Type::named("Numeric")
    );
    assert_eq!(Type::Integer.meet(&Type::named("Numeric")), Type::Integer);
    assert_eq!(Type::Integer.meet(&Type::String), Type::Never);
    let dynamic_array = Type::Array(Box::new(Type::Any));
    let call_node_array = Type::Array(Box::new(Type::named("Prism::CallNode")));
    assert_eq!(dynamic_array.join(&call_node_array), dynamic_array);
    assert_eq!(call_node_array.join(&dynamic_array), dynamic_array);
    assert_eq!(
        Type::union([call_node_array, dynamic_array.clone()]),
        dynamic_array
    );
    assert_eq!(
        Type::intersection([Type::Integer, Type::String]),
        Type::Never
    );
    assert_eq!(typey::signature::parse_type("::Object"), Type::Object);
    assert_eq!(
        typey::signature::parse_type("::Array[Integer]"),
        Type::Array(Box::new(Type::Integer))
    );
    assert_eq!(
        typey::signature::parse_type("T.proc.params(value: Integer).returns(String)"),
        Type::Proc(vec![Type::Integer], Box::new(Type::String))
    );
    assert_eq!(
        typey::signature::parse_type("^-> void"),
        Type::Proc(Vec::new(), Box::new(Type::Nil))
    );
    assert_eq!(
        typey::signature::parse_type("^(String path) -> Array[Offense]"),
        Type::Proc(
            vec![Type::String],
            Box::new(Type::Array(Box::new(Type::named("Offense")))),
        )
    );
    assert_eq!(
        typey::signature::parse_type("[Integer, String]"),
        Type::Tuple(vec![Type::Integer, Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("Array[(Integer, String)]"),
        Type::Array(Box::new(Type::Tuple(vec![Type::Integer, Type::String])))
    );
    assert_eq!(
        typey::signature::parse_type("singleton(Example)"),
        Type::Named("Class".to_owned(), vec![Type::named("Example")])
    );
    assert_eq!(
        typey::signature::parse_type("T::Class[Example]"),
        Type::Named("Class".to_owned(), vec![Type::named("Example")])
    );
    assert!(Type::Integer.is_subtype_of(&Type::Object));
    assert!(Type::Tuple(vec![Type::Integer, Type::String])
        .is_subtype_of(&Type::Array(Box::new(Type::Object))));
}

#[test]
fn parses_rbs_continuations_by_default() {
    let source = "#: (Integer)\n#| -> String\ndef stringify(value)\n  value.to_s\nend\n";
    let annotations = typey::signature::collect(source);
    assert_eq!(annotations.methods["stringify"].params, vec![Type::Integer]);
    assert_eq!(annotations.methods["stringify"].return_type, Type::String);
    assert_eq!(annotations.methods["stringify"].required_params, 1);
    assert!(!annotations.methods["stringify"].accepts_rest);
}

#[test]
fn tracks_optional_and_rest_rbs_parameters_for_calls() {
    let optional = typey::signature::parse_rbs_signature("(?Integer, String?) -> String").unwrap();
    assert_eq!(optional.required_params, 1);
    assert_eq!(optional.params.len(), 2);
    let rest = typey::signature::parse_rbs_signature("(Integer, *String) -> String").unwrap();
    assert_eq!(rest.required_params, 1);
    assert!(rest.accepts_rest);
}

#[test]
fn accepts_sorbet_rbs_assertion_spacing_and_comment_tails() {
    let source = "value = nil #: as !nil # trailing comment\nother = 1#:as String\n";
    let annotations = typey::signature::collect(source);
    assert_eq!(
        annotations.assertions[&0].kind,
        typey::signature::AssertionKind::Must
    );
    assert_eq!(
        annotations.assertions[&1].kind,
        typey::signature::AssertionKind::Cast
    );
    assert_eq!(annotations.assertions[&1].type_, Type::String);
}

#[test]
fn parses_rbs_comments_without_a_magic_comment() {
    let source = "value = 1 #: Integer\n";
    let annotations = typey::signature::collect(source);
    assert_eq!(annotations.assertions[&0].type_, Type::Integer);
}

#[test]
fn parses_rbs_type_alias_comments() {
    let annotations =
        typey::signature::collect("module Example\n  #: type Node = Integer | String\nend\n");
    assert_eq!(
        annotations.type_aliases.get("Node"),
        Some(&Type::union([Type::Integer, Type::String]))
    );

    let spoom_source = include_str!("../test_repos/spoom/lib/spoom/ext/prism_types.rb");
    let spoom_annotations = typey::signature::collect(spoom_source);
    assert!(spoom_annotations.type_aliases.contains_key("anyScopeNode"));
    assert_eq!(
        spoom_annotations.type_aliases["anyScopeNode"],
        Type::union([
            Type::named("Prism::ClassNode"),
            Type::named("Prism::ModuleNode"),
            Type::named("Prism::SingletonClassNode"),
        ])
    );
    assert_eq!(
        typey::signature::parse_type("PrismTypes::anyScopeNode"),
        Type::named("PrismTypes::anyScopeNode")
    );
}

#[test]
fn expands_rbs_type_aliases_in_signatures() {
    let source =
        "#: type Value = Integer\n#: (Value) -> void\ndef accept(value)\nend\n\naccept(\"x\")\n";
    let result = check(source, CheckerConfig::default());
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Expected `Integer`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn applies_rbs_type_aliases_to_inline_assertions() {
    let source = "module PrismTypes\n  #: type anyScopeNode = Integer | String\nend\n\nvalue = 1 #: PrismTypes::anyScopeNode\n";
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn parses_multiline_sorbet_sig_blocks() {
    let source = "sig do\n  params(value: Integer)\n    .returns(String)\nend\ndef stringify(value)\n  value.to_s\nend\n";
    let annotations = typey::signature::collect(source);
    assert_eq!(annotations.methods["stringify"].params, vec![Type::Integer]);
    assert_eq!(annotations.methods["stringify"].return_type, Type::String);
}

#[test]
fn ast_annotation_collection_ignores_fixture_text() {
    let source = "class Example\n  sig { params(value: Integer).returns(Integer) }\n  def convert(value)\n    value\n  end\n\n  fixture = <<~RUBY\n    sig { params(value: String).returns(String) }\n    def convert(value)\n      value\n    end\n  RUBY\nend\n";
    let parsed = typey::prism::parse(source.as_bytes());
    let annotations = typey::signature::collect_for_ast(source, &parsed.node());
    assert_eq!(annotations.method_annotations.len(), 1);
    let signature = annotations
        .method_annotations
        .values()
        .next()
        .and_then(|signatures| signatures.first())
        .expect("real definition has a signature");
    assert_eq!(signature.params, vec![Type::Integer]);
    assert_eq!(signature.return_type, Type::Integer);
}

#[test]
fn checks_rbs_and_sorbet_keyword_arguments_by_name() {
    let source = r#"#: (value: String, ?suffix: String) -> String
def rbs_join(value:, suffix: "")
  value + suffix
end

sig { params(value: String, suffix: String).returns(String) }
def sorbet_join(value:, suffix: "")
  value + suffix
end

rbs_join(value: "a", suffix: "b")
sorbet_join(value: "a", suffix: "b")
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn uses_declared_inheritance_for_assignability() {
    let source = r#"class Parent
end

class Child < Parent
end

#: (Parent) -> void
def accept(value)
end

accept(Child.new)
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn resolves_nested_inheritance_and_class_objects() {
    let source = r#"module Outer
  class Parent
  end

  class Child < Parent
  end
end

#: (Outer::Parent) -> void
def accept(value)
end

#: (Class[Outer::Parent]) -> void
def accept_class(value)
end

accept(Outer::Child.new)
accept_class(Outer::Child)
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn refines_or_assignments_to_the_non_nil_rhs() {
    let source = r#"class Example
  #: -> Example
  def value
    @value ||= Example.new #: Example?
  end
end
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn narrows_assignment_predicates() {
    let source = r#"class Node
end

#: -> Node?
def maybe_node
  Node.new
end

#: (Node) -> void
def use_node(node)
end

if (node = maybe_node)
  use_node(node)
end
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn models_hash_fetch_and_array_concat() {
    let source = r#"#: (String) -> void
def use_string(value)
end

#: (Array[String?]) -> void
def use_array(value)
end

hash = {} #: Hash[String, String]
use_string(hash.fetch("name"))

current_namespace_path = [] #: Array[String?]
resolved_constant = [""].concat(current_namespace_path)
use_array(resolved_constant)
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn checks_rbs_proc_annotations_and_block_arity() {
    let source = r#"def interrupt_callback
  -> { nil } #: ^-> void
end

def process_file_proc
  proc do |path|
    [path]
  end #: ^(String path) -> Array[String]
end
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

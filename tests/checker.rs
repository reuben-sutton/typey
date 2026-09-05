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
        typey::signature::parse_type("[Integer, String]"),
        Type::Tuple(vec![Type::Integer, Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("Array[(Integer, String)]"),
        Type::Array(Box::new(Type::Tuple(vec![Type::Integer, Type::String])))
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

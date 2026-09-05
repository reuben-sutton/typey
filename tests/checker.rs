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
    assert!(Type::Integer.is_subtype_of(&Type::Object));
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

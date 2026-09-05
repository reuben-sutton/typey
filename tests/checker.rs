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

    let invalid_fixed_member = check(
        r#"
class Fixed
  extend T::Sig
  extend T::Generic
  Elem = type_member { {fixed: Integer} }

  sig { returns(Elem) }
  def value
    "wrong"
  end
end
"#,
        CheckerConfig::default(),
    );
    assert!(
        invalid_fixed_member
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic
                .message
                .contains("Expected method `value` to return `Integer`, but found `String`")),
        "{:?}",
        invalid_fixed_member.diagnostics
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
fn covers_unless_until_and_begin_else_flow() {
    let result = check(
        r#"
flag = nil #: String?
unless flag
  T.reveal_type(flag)
end

until false
  break "done"
end
loop_result = until false
  break "done"
end
T.reveal_type(loop_result)

begin_result = begin
  1
rescue StandardError
  2
else
  "completed"
end
T.reveal_type(begin_result)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `NilClass`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.nilable(String)`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.any(Integer, String)`")),
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
    assert_eq!(
        typey::signature::parse_type("T.attached_class"),
        Type::AttachedClass
    );
    assert!(Type::Integer.is_subtype_of(&Type::Object));
    assert!(Type::Tuple(vec![Type::Integer, Type::String])
        .is_subtype_of(&Type::Array(Box::new(Type::Object))));
}

#[test]
fn exercises_structural_lattice_operations() {
    assert_eq!(
        Type::Array(Box::new(Type::Integer)).join(&Type::Array(Box::new(Type::String))),
        Type::Array(Box::new(Type::union([Type::Integer, Type::String])))
    );
    assert_eq!(
        Type::Hash(Box::new(Type::String), Box::new(Type::Integer))
            .join(&Type::Hash(Box::new(Type::String), Box::new(Type::Float),)),
        Type::Hash(
            Box::new(Type::String),
            Box::new(Type::union([Type::Float, Type::Integer])),
        )
    );
    assert_eq!(
        Type::Tuple(vec![Type::Integer, Type::String])
            .join(&Type::Tuple(vec![Type::Float, Type::String,])),
        Type::Tuple(vec![
            Type::union([Type::Float, Type::Integer]),
            Type::String
        ])
    );
    assert_eq!(
        Type::Named("Box".to_owned(), vec![Type::Integer])
            .join(&Type::Named("Box".to_owned(), vec![Type::String],)),
        Type::Named(
            "Box".to_owned(),
            vec![Type::union([Type::Integer, Type::String])],
        )
    );
    assert_eq!(
        Type::Proc(vec![Type::Integer], Box::new(Type::String))
            .join(&Type::Proc(vec![Type::Integer], Box::new(Type::Symbol),)),
        Type::Proc(
            vec![Type::Integer],
            Box::new(Type::union([Type::String, Type::Symbol])),
        )
    );
    assert_eq!(
        Type::union([Type::Integer, Type::String]).meet(&Type::Integer),
        Type::Integer
    );
    assert_eq!(
        Type::union([Type::Nil, Type::False, Type::String]).truthy_part(),
        Type::String
    );
    assert_eq!(
        Type::union([Type::Nil, Type::False, Type::String]).falsy_part(),
        Type::union([Type::False, Type::Nil])
    );
    assert_eq!(
        Type::union([Type::Nil, Type::Integer]).without(&Type::Nil),
        Type::Integer
    );
    assert_eq!(
        Type::intersection([Type::Object, Type::String]),
        Type::String
    );
    assert!(Type::Proc(vec![Type::Object], Box::new(Type::Integer))
        .is_subtype_of(&Type::Proc(vec![Type::Integer], Box::new(Type::Object))));
}

#[test]
fn parses_the_supported_advanced_sorbet_type_forms() {
    assert_eq!(
        typey::signature::parse_type("T.nilable(String)"),
        Type::union([Type::Nil, Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("T.any(Integer, String)"),
        Type::union([Type::Integer, Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("T.all(Object, String)"),
        Type::intersection([Type::Object, Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("T.class_of(String)"),
        Type::Named("Class".to_owned(), vec![Type::String])
    );
    assert_eq!(
        typey::signature::parse_type("T.type_parameter(:U)"),
        Type::TypeVar("U".to_owned())
    );
    assert_eq!(
        typey::signature::parse_type("T.proc.params(value: String).returns(Integer)"),
        Type::Proc(vec![Type::String], Box::new(Type::Integer))
    );
    assert_eq!(
        typey::signature::parse_type("T::Map[String, Integer]"),
        Type::Named("T::Map".to_owned(), vec![Type::String, Type::Integer],)
    );

    let signature = typey::signature::parse_sorbet_signature(
        "sig { type_parameters(:U, :V).params(value: U, other: V).returns(T.nilable(U)) }",
    )
    .expect("signature parses");
    assert_eq!(signature.type_parameters, vec!["U", "V"]);
    assert_eq!(
        signature.params,
        vec![Type::TypeVar("U".into()), Type::TypeVar("V".into())]
    );
    assert_eq!(
        signature.return_type,
        Type::union([Type::Nil, Type::TypeVar("U".into())])
    );

    assert_eq!(
        typey::signature::parse_sorbet_type_alias("T.type_alias { T::Array[String] }"),
        Some(Type::Array(Box::new(Type::String)))
    );
    assert_eq!(
        typey::signature::parse_rbs_type_alias("type Result = Integer | String"),
        Some((
            "Result".to_owned(),
            Type::union([Type::Integer, Type::String])
        ))
    );
}

#[test]
fn specializes_attached_class_through_inherited_class_methods() {
    let result = check(
        r#"
class Base
  extend T::Sig

  sig { returns(T.attached_class) }
  def self.build
    new
  end
end

class Child < Base
end

T.reveal_type(Base.build)
T.reveal_type(Child.build)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Base`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Child`")),
        "{notes:?}"
    );
}

#[test]
fn specializes_multiple_generic_members_in_declaration_order() {
    let result = check(
        r#"
class Pair
  extend T::Sig
  extend T::Generic
  Zed = type_member
  Alpha = type_member

  sig { params(first: Zed, second: Alpha).returns(T::Hash[Alpha, Zed]) }
  def pair(first, second)
    {second => first}
  end
end

T.reveal_type(Pair[Integer, String].new.pair(1, "value"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Hash[String, Integer]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn specializes_nested_method_type_parameters() {
    let result = check(
        r#"
extend T::Sig

sig {
  type_parameters(:U)
    .params(values: T::Array[T.type_parameter(:U)])
    .returns(T.nilable(T.type_parameter(:U)))
}
def first(values)
  values[0]
end

T.reveal_type(first([1]))
T.reveal_type(first(["value"]))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.nilable(Integer)`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.nilable(String)`")),
        "{notes:?}"
    );
}

#[test]
fn specializes_type_parameters_inside_hashes() {
    let result = check(
        r#"
extend T::Sig

sig {
  type_parameters(:U)
    .params(values: T::Hash[String, T.type_parameter(:U)])
    .returns(T::Array[T.nilable(T.type_parameter(:U))])
}
def values_to_array(values)
  [values["value"]]
end

T.reveal_type(values_to_array({"value" => 1}))
T.reveal_type(values_to_array({"value" => "text"}))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[T.nilable(Integer)]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[T.nilable(String)]`")),
        "{notes:?}"
    );
}

#[test]
fn specializes_attached_and_self_types_through_inheritance() {
    let result = check(
        r#"
class Base
  extend T::Sig

  sig { returns(T::Array[T.attached_class]) }
  def self.instances
    [new]
  end

  sig { returns(T.nilable(T.self_type)) }
  def maybe_self
    self if true
  end
end

class Child < Base
end

T.reveal_type(Child.instances)
T.reveal_type(Child.new.maybe_self)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[Child]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.nilable(Child)`")),
        "{notes:?}"
    );
}

#[test]
fn preserves_concrete_types_through_core_models() {
    let result = check(
        r#"
values = [1, 2]
T.reveal_type(values.map { |value| value.to_s })
T.reveal_type(values.first)
T.reveal_type({"answer" => 1}.fetch("answer"))
T.reveal_type("42".to_i)
T.reveal_type(1 + 2)
T.reveal_type(T.must(1))
T.reveal_type(T.nilable(1))
T.reveal_type(T.unsafe(1))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `T::Array[String]`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `Integer`",
        "Revealed type: `T.untyped`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
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
fn reports_signature_and_call_type_errors_precisely() {
    let result = check(
        r#"
extend T::Sig

sig { params(value: Integer).returns(String) }
def stringify(value)
  value
end

stringify("wrong")
"#,
        CheckerConfig::default(),
    );
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(
        errors.iter().any(|message| message
            .contains("Expected method `stringify` to return `String`, but found `Integer`")),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|message| message.contains("Expected `Integer`, but found `String`")),
        "{errors:?}"
    );
    assert!(
        !errors.iter().any(|message| message.contains("T.untyped")),
        "{errors:?}"
    );
}

#[test]
fn reports_overload_and_argument_shape_errors() {
    let result = check(
        r#"
extend T::Sig

sig { params(value: String).returns(String) }
sig { params(value: Integer).returns(Integer) }
def identity(value)
  value
end

identity(:bad)

#: (String, ?String) -> String
def optional(value, suffix = "")
  value + suffix
end

optional()
optional("a", "b", "c")

#: (value: String, ?suffix: String) -> String
def keyword_join(value:, suffix: "")
  value + suffix
end

keyword_join
keyword_join(value: "a", extra: "!")
"#,
        CheckerConfig::default(),
    );
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 5, "{errors:?}");
    assert_eq!(
        errors
            .iter()
            .filter(|message| message.contains("Expected `T.any(Integer, String)"))
            .count(),
        1,
        "{errors:?}"
    );
    assert_eq!(
        errors
            .iter()
            .filter(|message| message.contains("Wrong number of arguments for `optional`"))
            .count(),
        2,
        "{errors:?}"
    );
    assert_eq!(
        errors
            .iter()
            .filter(|message| message.contains("Wrong number of arguments for `keyword_join`"))
            .count(),
        2,
        "{errors:?}"
    );
}

#[test]
fn preserves_concrete_types_through_nil_safe_dispatch() {
    let result = check(
        r#"
value = "text" #: String?
T.reveal_type(value&.length)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T.nilable(Integer)`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn checks_sorbet_assertion_helpers_and_absurd() {
    let result = check(
        r#"
value = T.let(1, Integer)
asserted = T.assert_type!(value, Integer)
casted = T.cast("text", String)
maybe = T.nilable(1)

T.reveal_type(asserted)
T.reveal_type(casted)
T.reveal_type(T.must(maybe))
T.reveal_type(T.unsafe(value))
T.absurd(1)
"#,
        CheckerConfig::default(),
    );
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0]
            .message
            .contains("Expected `T.noreturn`, but found `Integer`"),
        "{errors:?}"
    );
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        2,
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.untyped`")),
        "{notes:?}"
    );
}

#[test]
fn carries_proc_and_block_types_through_calls() {
    let result = check(
        r#"
stringify = ->(value) { value.to_s }
T.reveal_type(stringify)
T.reveal_type(stringify.call(1))

mapped = [1, 2].map { |value| value.to_s }
T.reveal_type(mapped)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes.iter().any(|message| {
            message.contains("Revealed type: `T.proc.params(T.untyped).returns(String)`")
        }),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[String]`")),
        "{notes:?}"
    );
}

#[test]
fn preserves_concrete_types_through_collection_and_primitive_methods() {
    let result = check(
        r#"
values = [1, 2, 3]
maybe_values = [nil, "text"]
hash = {"answer" => 1}

T.reveal_type(values.size)
T.reveal_type(values[0])
T.reveal_type(values["slice"])
T.reveal_type(values.compact)
T.reveal_type(maybe_values.compact)
T.reveal_type(values.filter_map { |value| value.even? ? value.to_s : nil })
T.reveal_type(values.filter_map { |value| value.even? ? value.to_s : false })
T.reveal_type(values.join(","))
T.reveal_type(values.to_a)
T.reveal_type(hash.keys)
T.reveal_type(hash.values)
T.reveal_type(hash.fetch("answer", 0.0))
T.reveal_type(hash.length)
T.reveal_type("a b".split)
T.reveal_type("a".to_sym)
T.reveal_type(1 / 2)
T.reveal_type(1 / 2.0)
T.reveal_type(1.even?)
T.reveal_type(T.unsafe(nil).to_s)
T.reveal_type(T.unsafe(nil).nil?)
T.reveal_type(T.unsafe(nil).to_a)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `Integer`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `String`",
        "Revealed type: `T::Array[String]`",
        "Revealed type: `T.any(Float, Integer)`",
        "Revealed type: `T::Array[T.untyped]`",
        "Revealed type: `T::Boolean`",
        "Revealed type: `Symbol`",
        "Revealed type: `Float`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        3,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Array[String]`"))
            .count(),
        5,
        "{notes:?}"
    );
}

#[test]
fn preserves_container_types_through_iteration_blocks() {
    let result = check(
        r#"
values = [1, 2, 3]
hash = {"answer" => 1}

T.reveal_type(values.each_with_index { |value, index| value + index })
T.reveal_type(values.select { |value| value.even? })
T.reveal_type(hash.each { |key, value| value.to_s })
T.reveal_type(hash.each_key { |key| key.to_sym })
T.reveal_type(hash.each_value { |value| value.to_s })
T.reveal_type(hash.fetch("answer") { |key| key.length })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Array[Integer]`"))
            .count(),
        2,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Hash[String, Integer]`"))
            .count(),
        3,
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Integer`")),
        "{notes:?}"
    );
}

#[test]
fn preserves_types_through_literal_splats() {
    let result = check(
        r#"
values = [1, 2]
hash = {"answer" => 1}

T.reveal_type([0, *values])
T.reveal_type({"other" => 2, **hash})
T.reveal_type({**hash})
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Array[Integer]`"))
            .count(),
        1,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Hash[String, Integer]`"))
            .count(),
        2,
        "{notes:?}"
    );
}

#[test]
fn preserves_collection_transform_types() {
    let result = check(
        r#"
values = [1, 2]
hash = {"answer" => 1}

T.reveal_type(values.first(1))
T.reveal_type(values.last(1))
T.reveal_type(values.fetch(0))
T.reveal_type(values.fetch(0, 0.0))
T.reveal_type(values.fetch(0) { |index| index.to_s })
T.reveal_type(values + [2.0])
T.reveal_type(hash.merge({"other" => "text"}))
T.reveal_type(hash.transform_values { |value| value.to_s })
T.reveal_type(hash.to_a)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `Integer`",
        "Revealed type: `T.any(Float, Integer)`",
        "Revealed type: `T::Array[T.any(Float, Integer)]`",
        "Revealed type: `T::Hash[String, T.any(Integer, String)]`",
        "Revealed type: `T::Hash[String, T.any(Integer, String)]`",
        "Revealed type: `T::Array[[String, Integer]]`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn tracks_local_compound_assignments() {
    let result = check(
        r#"
value = 1
value += 2.0
T.reveal_type(value)

flag = true
flag &&= "done"
T.reveal_type(flag)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Float`"))
            .count(),
        1,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        1,
        "{notes:?}"
    );
}

#[test]
fn preserves_built_in_class_object_and_global_call_types() {
    let result = check(
        r#"
T.reveal_type(Array.new)
T.reveal_type(Hash.new)
T.reveal_type(Integer("1"))
T.reveal_type(Float("1.0"))
T.reveal_type(String(1))
T.reveal_type(Symbol("name"))
T.reveal_type(rand)
T.reveal_type(sleep(0))
T.reveal_type(puts("ignored"))
T.reveal_type(T.any(1, "value"))
T.reveal_type(T.any(Integer, String))
T.reveal_type(T.all(Object, String))
T.reveal_type(T.nilable(String))
T.reveal_type(T.bind(1, Integer))
T.reveal_type(T.cast(1, String))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `Array`",
        "Revealed type: `Hash`",
        "Revealed type: `Integer`",
        "Revealed type: `Float`",
        "Revealed type: `String`",
        "Revealed type: `Symbol`",
        "Revealed type: `NilClass`",
        "Revealed type: `T.any(Integer, String)`",
        "Revealed type: `T.nilable(String)`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        3,
        "{notes:?}"
    );
}

#[test]
fn narrows_array_hash_and_alternation_patterns() {
    let result = check(
        r#"
values = [1, "two"]
case values
in [Integer, String]
  T.reveal_type(values)
else
  nil
end

record = {answer: 1}
case record
in answer: answer
  T.reveal_type(answer)
else
  nil
end

choice = 1
case choice
in Integer | String
  T.reveal_type(choice)
else
  nil
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[T.any(Integer, String)]`")),
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        2,
        "{notes:?}"
    );
}

#[test]
fn infers_sorbet_method_type_parameters_at_each_call_site() {
    let result = check(
        r#"
extend T::Sig

sig { type_parameters(:U).params(value: T.type_parameter(:U)).returns(T.type_parameter(:U)) }
def identity(value)
  value
end

T.reveal_type(identity(1))
T.reveal_type(identity("value"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Integer`")),
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
fn preserves_unbound_sorbet_type_parameters_and_checks_method_bodies() {
    let result = check(
        r#"
extend T::Sig

sig { type_parameters(:U).returns(T.type_parameter(:U)) }
def unresolved
  1
end

T.reveal_type(unresolved)
"#,
        CheckerConfig::default(),
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Expected method `unresolved` to return `U`, but found `Integer`")
        }),
        "{:?}",
        result.diagnostics
    );
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `U`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn specializes_sorbet_generic_type_members() {
    let result = check(
        r#"
class Box
  extend T::Sig
  extend T::Generic
  Elem = type_member

  sig { params(value: Elem).returns(Elem) }
  def identity(value)
    value
  end
end

class Fixed
  extend T::Sig
  extend T::Generic
  Elem = type_member { {fixed: Integer} }

  sig { returns(Elem) }
  def value
    1
  end
end

T.reveal_type(Box[Integer].new.identity(1))
T.reveal_type(Box[String].new.identity("value"))
T.reveal_type(Box.new.identity(1))
T.reveal_type(Fixed.new.value)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        3,
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
fn specializes_sorbet_type_template_members() {
    let result = check(
        r#"
class Box
  extend T::Sig
  extend T::Generic
  Template = type_template

  sig { params(value: Template).returns(Template) }
  def identity(value)
    value
  end
end

T.reveal_type(Box[Integer].new.identity(1))
T.reveal_type(Box[String].new.identity("value"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        1,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `String`"))
            .count(),
        1,
        "{notes:?}"
    );
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

#[test]
fn preserves_struct_subclass_constant_identity() {
    let source = r#"module Node
  Location = Struct.new(:line, :column)

  #: -> Node::Location
  def self.build
    Location.new(1, 2)
  end
end
"#;
    let result = check(source, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

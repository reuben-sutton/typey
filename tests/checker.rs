use std::path::Path;

use typey::diagnostic::Severity;
use typey::{
    builtin_rbi_paths, check, check_workspace, load_workspace_paths, CheckerConfig, Type,
    TypeLattice, WorkspaceFile,
};

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
fn reports_missing_methods_in_typed_true_files() {
    check_fixture("tests/fixtures/typed_true_missing_api.rb");
}

#[test]
fn distinguishes_static_top_from_untyped() {
    let result = check_fixture("tests/fixtures/static_top.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `T.anything`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn enforces_private_class_method_visibility() {
    let result = check_fixture("tests/fixtures/private_methods.rb");
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic
                .message
                .contains("Non-private call to private method `consume`"))
            .count(),
        1,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_the_static_top_for_bare_class_annotations() {
    let result = check_fixture("tests/fixtures/bare_class_generic.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `Class[T.anything]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_nominal_predicates_to_unreachable_when_classes_are_disjoint() {
    let result = check_fixture("tests/fixtures/nominal_predicate_unreachable.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `First`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn checks_splat_call_shapes() {
    check_fixture("tests/fixtures/splat_comparison.rb");
}

#[test]
fn dispatches_declared_methods_through_polymorphic_receivers() {
    let result = check_fixture("tests/fixtures/polymorphic_method_dispatch.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T.any(Integer, String)`")),
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
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `Integer`"))
            .count(),
        1,
        "{notes:?}"
    );
}

#[test]
fn specializes_namespaced_generic_members_at_dispatch() {
    let result = check_fixture("tests/fixtures/namespaced_generic_member_dispatch.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn applies_short_rbs_types_to_generated_accessors() {
    let result = check_fixture("tests/fixtures/short_attribute_type_annotations.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_array_types_through_must_on_slices() {
    let result = check_fixture("tests/fixtures/must_array_slice.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn propagates_typed_keyword_arguments_into_must_ivar_reads() {
    let result = check_fixture("tests/fixtures/typed_keyword_ivar_must.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_numeric_unary_methods() {
    let result = check_fixture("tests/fixtures/numeric_unary.rb");
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
        2,
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
fn models_integer_bitwise_operators() {
    let result = check_fixture("tests/fixtures/integer_bitwise.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Integer`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_class_object_methods() {
    let result = check_fixture("tests/fixtures/class_object_builtins.rb");
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    for expected in [
        "Revealed type: `T::Boolean`",
        "Revealed type: `T.nilable([String, Integer])`",
        "Revealed type: `T.noreturn`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn models_array_range_slices_as_nilable() {
    let result = check(
        r#"
values = [1, "text"]
T.reveal_type(values[1..])
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T.nilable(T::Array[T.any(Integer, String)])`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn dispatches_short_names_and_structural_builtins() {
    let result = check_fixture("tests/fixtures/common_builtin_dispatch.rb");
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
        6,
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[Integer]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Hash[String, Integer]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Boolean`")),
        "{notes:?}"
    );
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
        2,
        "{notes:?}"
    );
}

#[test]
fn indexes_inline_record_types() {
    let result = check_fixture("tests/fixtures/inline_record_dispatch.rb");
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
fn gives_included_methods_the_host_self_type() {
    let result = check_fixture("tests/fixtures/mixin_self_dispatch.rb");
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")));
}

#[test]
fn prefers_direct_class_methods_over_extended_module_methods() {
    let result = check_fixture("tests/fixtures/direct_class_method_precedes_extension.rb");
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")));
}

#[test]
fn visits_hash_sort_by_blocks() {
    let result = check_fixture("tests/fixtures/hash_sort_by_block.rb");
    assert!(result.diagnostics.iter().any(|diagnostic| diagnostic
        .message
        .contains("Revealed type: `T::Array[[String, Integer]]`")));
}

#[test]
fn destructures_typed_tuple_elements_in_collection_blocks() {
    let result = check_fixture("tests/fixtures/tuple_block_destructuring.rb");
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
            .any(|message| message.contains("Revealed type: `Integer`")),
        "{notes:?}"
    );
}

#[test]
fn preserves_typed_ivar_elements_through_empty_resets() {
    let result = check_fixture("tests/fixtures/typed_ivar_empty_reset.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn inherits_typed_ivars_from_superclasses() {
    let result = check_fixture("tests/fixtures/inherited_typed_ivar.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_generic_types_for_runtime_constructors() {
    let result = check_fixture("tests/fixtures/generic_runtime_constructors.rb");
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
            .any(|message| message.contains("Revealed type: `T::Array[Integer]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Hash[String, Integer]`")),
        "{notes:?}"
    );
}

#[test]
fn instantiates_builtin_generic_classes_without_erasing_the_element_type() {
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs load"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new(
        "builtin_generic_constructors.rb",
        r#"# typed: true

T.reveal_type(Array.new)
T.reveal_type(File.new("fixture", "r").first)
"#,
    ));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `T::Array[T.untyped]`")),
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
fn infers_empty_generic_defaults_from_parameter_types() {
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs load"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new(
        "generic_default.rb",
        r#"# typed: true

class UsesSet
  #: (?Set[String]) -> void
  def initialize(values = T.reveal_type(Set.new))
  end
end
"#,
    ));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .diagnostic
                .message
                .contains("Revealed type: `Set[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_generic_hash_types_from_nested_pair_arrays() {
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs load"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new(
        "generic_hash_pairs.rb",
        "# typed: true\nT.reveal_type(Hash[[[1, 2]]])\n",
    ));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .diagnostic
            .message
            .contains("Revealed type: `T::Hash[Integer, Integer]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn treats_setter_calls_as_the_assigned_value() {
    let result = check_fixture("tests/fixtures/setter_assignment.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn preserves_generic_accessor_types_through_nested_iteration() {
    let result = check_fixture("tests/fixtures/generic_accessor_iteration.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Integer`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_nilable_locals_after_safe_navigation_guards() {
    let result = check_fixture("tests/fixtures/safe_navigation_narrowing.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn rejects_safe_navigation_on_definitely_non_nil_receivers() {
    check_fixture("tests/fixtures/safe_navigation_non_nil.rb");
}

#[test]
fn narrows_unions_for_equality_predicates() {
    let result = check_fixture("tests/fixtures/equality_predicate_narrowing.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn reports_unreachable_statement_branches() {
    check_fixture("tests/fixtures/unreachable_control_flow.rb");
}

#[test]
fn reports_unreachable_nominal_predicate_next() {
    check_fixture("tests/fixtures/nominal_predicate_next.rb");
}

#[test]
fn narrows_class_objects_by_subclass_comparisons() {
    let result = check_fixture("tests/fixtures/class_object_subclass_narrowing.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn dispatches_class_object_methods_through_intersections() {
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs load"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new(
        "class_object_intersection.rb",
        r#"# typed: true

module Exportable
  extend T::Sig
  sig { returns(Integer) }
  def export
    0
  end
end

class Base
  extend T::Sig
  sig { params(value: String).returns(T.nilable(T.attached_class)) }
  def self.find(value); end
end

extend T::Sig
sig { params(klass: T.class_of(Base)).void }
def deserialize(klass)
  if klass < Exportable
    value = klass.find("foo")
    T.reveal_type(value)
    raise unless value
    T.reveal_type(value)
    exported = value.export
    T.reveal_type(exported)
  end
end
"#,
    ));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        notes.iter().any(|message| message.contains("T.nilable")),
        "{notes:?}"
    );
    assert!(
        notes.iter().any(|message| message.contains("T.all")),
        "{notes:?}"
    );
    assert!(
        notes.iter().any(|message| message.contains("Integer")),
        "{notes:?}"
    );
}

#[test]
fn preserves_nil_for_locals_assigned_only_in_unreached_rescues() {
    let result = check_fixture("tests/fixtures/rescue_definite_assignment.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `NilClass`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_array_intersection_predicates() {
    let result = check_fixture("tests/fixtures/array_intersect_predicate.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `T::Boolean`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_array_comparison() {
    let result = check_fixture("tests/fixtures/array_comparison.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T.nilable(Integer)`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn checks_array_comparison_return_contracts() {
    check_fixture("tests/fixtures/array_comparison_contract.rb");
}

#[test]
fn accepts_ranges_with_concrete_integer_endpoints_as_integer_ranges() {
    check_fixture("tests/fixtures/range_assignability.rb");
}

#[test]
fn models_random_formatter_keywords() {
    let result = check_fixture("tests/fixtures/random_formatter.rb");
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message.contains("Revealed type: `String`"))
            .count(),
        2,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_array_inspection_as_string() {
    let result = check(
        r#"
T.reveal_type(["unknown"].inspect)
T.reveal_type(["unknown"].to_s)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message.contains("Revealed type: `String`"))
            .count(),
        2,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_array_to_set() {
    let result = check_fixture("tests/fixtures/array_to_set.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Set[String]`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_set_predicates() {
    let result = check_fixture("tests/fixtures/set_predicate.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `T::Boolean`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_string_bang_methods() {
    let result = check_fixture("tests/fixtures/string_bang_methods.rb");
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T.nilable(String)`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_symbol_to_proc_collection_blocks() {
    let result = check_fixture("tests/fixtures/symbol_to_proc_map.rb");
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`"))
            .count(),
        2,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_string_shellescape() {
    let result = check_fixture("tests/fixtures/string_shellescape.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_rescue_references_to_the_exception_type() {
    let result = check_fixture("tests/fixtures/rescue_narrowing.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Integer`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_nested_rescue_collection_elements() {
    let result = check_fixture("tests/fixtures/nested_rescue_collection.rb");
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Integer`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn maps_nullable_proc_parameters_to_blocks() {
    check_fixture("tests/fixtures/nullable_block_signature.rb");
}

#[test]
fn preserves_optional_rbs_block_parameters() {
    check_fixture("tests/fixtures/optional_rbs_block.rb");
}

#[test]
fn treats_unannotated_block_parameters_as_optional() {
    let result = check_fixture("tests/fixtures/untyped_optional_block.rb");
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic.severity == Severity::Note
            && diagnostic.message.contains("Revealed type: `String`")
    }));
}

#[test]
fn does_not_assume_overridable_raising_methods_are_noreturn() {
    check_fixture("tests/fixtures/overridable_raising_method.rb");
}

#[test]
fn maps_arbitrary_and_anonymous_block_parameter_names() {
    let result = check_fixture("tests/fixtures/block_parameter_names.rb");
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("Revealed type: `Integer`")));
}

#[test]
fn narrows_case_after_terminating_type_branch() {
    let result = check_fixture("tests/fixtures/terminating_case_narrowing.rb");
    assert!(result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")));
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
fn propagates_blocks_through_super_calls() {
    let result = check(
        r#"
class Parent
  def call
    yield 1
  end
end

class Child < Parent
  def call
    super { |value| value.to_s }
  end
end

T.reveal_type(Child.new.call)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `String`")
        }),
        "{:?}",
        result.diagnostics
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
    assert!(dynamic_array.contains_any());
    assert!(!call_node_array.contains_any());
    assert_eq!(dynamic_array.join(&call_node_array), dynamic_array);
    assert_eq!(call_node_array.join(&dynamic_array), dynamic_array);
    assert_eq!(
        Type::union([call_node_array, dynamic_array.clone()]),
        dynamic_array
    );
    let mixed_string_union = Type::Union(vec![
        Type::Named("String".to_owned(), Vec::new()),
        Type::String,
    ]);
    let canonical_string_union = Type::union([mixed_string_union]);
    assert_eq!(
        Type::union([canonical_string_union.clone()]),
        canonical_string_union
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
        Type::union([Type::Nil, Type::Object]),
        Type::Union(vec![Type::Nil, Type::Object])
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
        typey::signature::parse_type(
            "T.any(\n  String,\n  Integer, # Numeric values are also accepted.\n  Float,\n)"
        ),
        Type::union([Type::String, Type::Integer, Type::Float])
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
    let benchmark_signature =
        typey::signature::parse_sorbet_signature("sig { params(blk: T.proc.void).returns(Float) }")
            .expect("benchmark signature parses");
    assert_eq!(benchmark_signature.return_type, Type::Float);
    assert!(!benchmark_signature.is_void);
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
fn keeps_implicit_class_body_new_as_an_instance_type() {
    let result = check(
        r#"
class Status
  #: Status
  ALIVE = new
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
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
fn models_core_global_and_file_calls() {
    let source = r#"
T.reveal_type(1.id)
T.reveal_type(File.read("path"))
T.reveal_type(File.write("path", "contents"))
T.reveal_type(require("library"))
T.reveal_type(require_relative("library"))
"#;
    let files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs"))
        .expect("vendored RBIs load");
    let mut files = files;
    files.push(WorkspaceFile::new("core_calls.rb", source));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.diagnostic.message.as_str())
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
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T::Boolean`"))
            .count(),
        2,
        "{notes:?}"
    );
}

#[test]
fn uses_typed_constants_from_rbis() {
    let files = vec![
        WorkspaceFile::new(
            "vendor/sorbet/rbi/core/encoding.rbi",
            "class Encoding < Object\n  ASCII_8BIT = T.let(T.unsafe(nil), Encoding)\nend\n",
        ),
        WorkspaceFile::new(
            "app.rb",
            "#: (Encoding) -> void\ndef accept_encoding(value); end\naccept_encoding(Encoding::ASCII_8BIT)\n",
        ),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn infers_builtin_generic_block_return_types() {
    let source = r#"
class Base
end

classes = Set.new([Base]) #: Set[Class[Base]]
instances = classes.map { |klass| klass.new }
T.reveal_type(instances)
"#;
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new("generic_block.rb", source));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.diagnostic.severity == Severity::Note
                && diagnostic
                    .diagnostic
                    .message
                    .contains("Revealed type: `T::Array[Base]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn does_not_require_inferred_hash_constructor_block() {
    let source = r#"
with_block = Hash.new { |key, value| value }
without_block = Hash.new(0)
"#;
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new("hash_constructor.rb", source));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn preserves_explicit_result_types_through_flat_map_blocks() {
    let result = check(
        r#"
class Result
end

class Validator
  #: (String) -> Result
  def call(value)
    Result.new
  end

  #: -> Array[Validator]
  def self.all
    [Validator.new]
  end
end

T.reveal_type(Validator.all.flat_map { |validator| validator.call("value") })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[Result]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn does_not_invent_block_arity_for_inferred_methods() {
    let result = check(
        r#"
module External
  def self.flat_map(*args, **kwargs, &block)
    nil
  end
end

processor = ->(value) { [value] }
External.flat_map(["value"], &processor)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn publishes_only_the_final_type_per_expression() {
    let source = "# typed: strict\n\n#: (String command) -> String\ndef exec(command)\n  command.to_s\nend\n";
    let result = check(source, CheckerConfig::default());
    let start = source.find("command.to_s").expect("call span");
    let types = result
        .types
        .iter()
        .filter(|inferred| inferred.start == start && inferred.end == start + "command.to_s".len())
        .collect::<Vec<_>>();
    assert_eq!(types.len(), 1, "duplicate final types: {types:?}");
    assert_eq!(
        types[0].type_,
        Type::String,
        "unexpected final type: {types:?}"
    );
    assert!(types[0].is_send, "send metadata was lost: {types:?}");
}

#[test]
fn infers_attr_reader_types_from_instance_variables() {
    let result = check(
        r#"
class Box
  attr_reader :value

  def initialize
    @value = 1
  end
end

T.reveal_type(Box.new.value)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `Integer`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn uses_declarations_on_attr_readers() {
    let result = check(
        r#"
class Box
  #: () -> String
  attr_reader :value
end

T.reveal_type(Box.new.value)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn uses_attribute_types_for_generated_writers() {
    let result = check_fixture("tests/fixtures/typed_attribute_writer.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_tuple_shape_when_pushing_into_typed_arrays() {
    let result = check_fixture("tests/fixtures/typed_tuple_array_push.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn widens_empty_local_array_accumulators_across_writes() {
    let result = check(
        r#"
values = []
values << "text"
values << 1
T.reveal_type(values)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Array[T.any(Integer, String)]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn treats_t_namespaced_enumerables_as_nominal_types() {
    let result = check_fixture("tests/fixtures/set_enumerable_assignability.rb");
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn prefers_builtin_rbi_signatures_over_untyped_gem_declarations() {
    let source = "# typed: true\n\nT.reveal_type(Benchmark.realtime { nil })\n";
    let mut files = load_workspace_paths(&builtin_rbi_paths().unwrap()).unwrap();
    files.push(WorkspaceFile::new("benchmark_realtime.rb", source));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .diagnostic
                .message
                .contains("Revealed type: `Float`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn specializes_tsort_results_from_the_graph_edge_type() {
    let source = r#"
class TypedGraph
  include TSort

  #: (T::Hash[String, T::Array[String]] edges) -> void
  def initialize(edges)
    @edges = edges
  end

  #: () ?{ (String node) -> void } -> void
  def tsort_each_node(&block)
    @edges.each_key(&block)
  end

  #: (String node) ?{ (String child) -> void } -> void
  def tsort_each_child(node, &block)
    (@edges[node] || []).each(&block)
  end

  def cycles
    @cycles ||= strongly_connected_components.reject { |component| component.length == 1 }
  end
end

graph = TypedGraph.new({"a" => ["b"], "b" => ["a"]})
T.reveal_type(graph.cycles)
"#;
    let mut files = load_workspace_paths(&builtin_rbi_paths().unwrap()).unwrap();
    files.push(WorkspaceFile::new("tsort_graph.rb", source));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .diagnostic
                .message
                .contains("Revealed type: `T::Array[T::Array[String]]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn resolves_module_function_definitions_on_module_receivers() {
    let result = check(
        r#"
module Helpers
  module_function def stringify(value)
    value.to_s
  end
end

T.reveal_type(Helpers.stringify(1))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn records_hash_calls_in_private_methods() {
    let source = r#"
class Tree
  def initialize
    @scores = {} #: Hash[String, Float]
  end

  private

  #: (String) -> Float
  def score(child)
    @scores.fetch(child, 0.0)
  end
end
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source
        .find("@scores.fetch(child, 0.0)")
        .expect("fetch call");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 25
    }));
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
fn propagates_yield_types_through_blocks() {
    let result = check(
        r#"
def wrapper
  yield 1
end

T.reveal_type(wrapper { |value| value.to_s })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `String`")
        }),
        "{:?}",
        result.diagnostics
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
fn preserves_concrete_types_through_more_core_methods() {
    let result = check(
        r#"
values = [1, 2, 3]

T.reveal_type(values.zip(["a"]))
T.reveal_type(values.flat_map { |value| [value.to_s] })
T.reveal_type(values.sum)
T.reveal_type(1.abs)
T.reveal_type(1.0.abs)
T.reveal_type("text".bytes)
T.reveal_type("text"[0])
T.reveal_type("text".gsub("t", "T"))
T.reveal_type("text".succ)
T.reveal_type("text".ord)
T.reveal_type("text".to_r)
T.reveal_type("text".to_c)
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
        "Revealed type: `T::Array[[Integer, String]]`",
        "Revealed type: `T::Array[String]`",
        "Revealed type: `Integer`",
        "Revealed type: `Float`",
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `T.nilable(String)`",
        "Revealed type: `String`",
        "Revealed type: `Rational`",
        "Revealed type: `Complex`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn preserves_literal_and_pseudo_expression_types() {
    let result = check(
        r#"
T.reveal_type(defined?(1))
T.reveal_type(1..3)
T.reveal_type(/text/)
T.reveal_type(__LINE__)
T.reveal_type(__FILE__)
T.reveal_type(__ENCODING__)
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
        "Revealed type: `T.nilable(String)`",
        "Revealed type: `Range[Integer, Integer]`",
        "Revealed type: `Regexp`",
        "Revealed type: `Integer`",
        "Revealed type: `String`",
        "Revealed type: `Encoding`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn preserves_range_endpoint_and_iteration_types() {
    let result = check(
        r#"
T.reveal_type((1..3).begin)
T.reveal_type((1..3).end)
T.reveal_type((1..3).exclude_end?)
T.reveal_type((1..3).to_a)
T.reveal_type((1..3).each { |value| value.to_s })
T.reveal_type((1..3).each)
T.reveal_type((1..3).first)
T.reveal_type((1..3).last)
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
        "Revealed type: `T::Boolean`",
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `Range[Integer, Integer]`",
        "Revealed type: `Enumerator`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn preserves_more_array_and_hash_collection_types() {
    let result = check(
        r#"
nested = [["a"], ["b"]]
values = [1, 2, 3]
hash = {"answer" => 1}

T.reveal_type(nested.flatten)
T.reveal_type(values.uniq)
T.reveal_type(values.each_index { |index| index.to_s })
T.reveal_type(values.find { |value| value.even? })
T.reveal_type(values.find_index { |value| value.even? })
T.reveal_type(values.group_by { |value| value.to_s })
T.reveal_type(values.partition { |value| value.even? })
T.reveal_type(values.take_while { |value| value.even? })
T.reveal_type(values.drop_while { |value| value.even? })
T.reveal_type(hash.invert)
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
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T::Hash[String, T::Array[Integer]]`",
        "Revealed type: `T::Array[T::Array[Integer]]`",
        "Revealed type: `T::Hash[Integer, String]`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn selects_find_without_fallback_when_optional_argument_is_omitted() {
    let result = check(
        r#"
class Finder
  sig do
    type_parameters(:U).params(
      ifnone: T.proc.returns(T.type_parameter(:U)),
      blk: T.proc.params(arg0: String).returns(T::Boolean)
    ).returns(T.any(T.type_parameter(:U), String))
  end
  sig do
    params(blk: T.proc.params(arg0: String).returns(T::Boolean))
      .returns(T.nilable(String))
  end
  def find(ifnone = nil, &blk)
    "value"
  end
end

T.reveal_type(Finder.new.find { |value| value.length > 0 })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T.nilable(String)`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_generic_block_returns_through_nilable_block_signatures() {
    let result = check(
        r#"
class Mapper
  sig do
    type_parameters(:U, :V).params(
      blk: T.nilable(
        T.proc.params(arg0: String).returns([
          T.type_parameter(:U),
          T.type_parameter(:V)
        ])
      )
    ).returns(T::Hash[T.type_parameter(:U), T.type_parameter(:V)])
  end
  def to_h(&blk)
    {}
  end
end

T.reveal_type(Mapper.new.to_h { |value| [value, value.length] })
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
fn preserves_pair_tuples_for_hash_from_collection_blocks() {
    let result = check(
        r#"
class HashBuilder
  class << self
    sig do
      type_parameters(:U, :V).params(
        entries: T.any(
          T::Array[[T.type_parameter(:U), T.type_parameter(:V)]],
          T::Hash[T.type_parameter(:U), T.type_parameter(:V)]
        )
      ).returns(T::Hash[T.type_parameter(:U), T.type_parameter(:V)])
    end
    def build(entries)
      {}
    end
  end
end

files = ["a", "b"]
T.reveal_type(HashBuilder.build(files.collect { |file| [file, file.length] }))
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
fn infers_dir_globs_as_string_arrays() {
    let result = check(
        r#"
files = Dir["*.rb"]
T.reveal_type(files)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Array[String]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_regexp_method_types() {
    let result = check(
        r#"
pattern = /text/

T.reveal_type(pattern.match("text"))
T.reveal_type(pattern.match?("text"))
T.reveal_type(pattern =~ "text")
T.reveal_type(pattern === "text")
T.reveal_type(pattern.source)
T.reveal_type(pattern.options)
T.reveal_type(pattern.encoding)
T.reveal_type("text".match(pattern))
T.reveal_type("text" =~ pattern)
T.reveal_type("text".match?(pattern))
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
        "Revealed type: `T.nilable(MatchData)`",
        "Revealed type: `T::Boolean`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `String`",
        "Revealed type: `Integer`",
        "Revealed type: `Encoding`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn preserves_more_string_and_numeric_method_types() {
    let result = check(
        r#"
T.reveal_type("abc".reverse)
T.reveal_type("abc".index("b"))
T.reveal_type("abc".encode)
T.reveal_type("abc".to_f)
T.reveal_type(1.fdiv(2))
T.reveal_type(1.round)
T.reveal_type(1.0.round(2))
T.reveal_type(1.ceil)
T.reveal_type(1.floor)
T.reveal_type(1.next)
T.reveal_type(1.gcd(2))
T.reveal_type(1.digits)
T.reveal_type(1.clamp(0, 2))
T.reveal_type(1.bit_length)
T.reveal_type(1.div(2))
T.reveal_type(1.divmod(2))
T.reveal_type(1.gcdlcm(2))
T.reveal_type(1.to_r)
T.reveal_type(1.to_c)
T.reveal_type(1.finite?)
T.reveal_type(1.infinite?)
T.reveal_type(1.imag)
T.reveal_type(1.times { |value| value.to_s })
T.reveal_type(1.upto(3) { |value| value.to_s })
T.reveal_type(1.downto(0))
T.reveal_type(1.step(3))
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
        "Revealed type: `String`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `Float`",
        "Revealed type: `Integer`",
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `Enumerator`",
        "Revealed type: `T::Array[[Integer, Integer]]`",
        "Revealed type: `Rational`",
        "Revealed type: `Complex`",
        "Revealed type: `T::Boolean`",
        "Revealed type: `T.nilable(Integer)`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn preserves_known_class_object_types() {
    let result = check(
        r#"
T.reveal_type(1.class)
T.reveal_type(1.0.class)
T.reveal_type("text".class)
T.reveal_type(:text.class)
T.reveal_type([1].class)
T.reveal_type({"answer" => 1}.class)
T.reveal_type(Object.new.class)
T.reveal_type(:text.to_sym)
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
        "Revealed type: `Class[Integer]`",
        "Revealed type: `Class[Float]`",
        "Revealed type: `Class[String]`",
        "Revealed type: `Class[Symbol]`",
        "Revealed type: `Class[Array]`",
        "Revealed type: `Class[Hash]`",
        "Revealed type: `Class[Object]`",
        "Revealed type: `Symbol`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn models_class_object_name() {
    let result = check(
        r#"
class Base
end

T.reveal_type(Base.name)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T.nilable(String)`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_nilable_local_after_replacing_it_in_unless() {
    let result = check(
        r#"
#: (String?) -> String?
def maybe_text(value)
  value
end

#: (String, String) -> void
def consume(first, second); end

first = maybe_text(nil)
unless first
  first = "fallback"
end
consume(first, "value")
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn keeps_non_exhaustive_integer_case_fallthrough_reachable() {
    let result = check(
        r#"
class Result
  #: () -> Integer
  def code
    0
  end
end

#: (Result) -> Integer
def code_after_cases(result)
  case result.code
  when 1
    raise "one"
  when 2
    raise "two"
  end
  result.code
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn does_not_treat_integer_constants_as_case_type_tests() {
    let result = check(
        r#"
FIRST = 1
SECOND = 2

#: (Integer) -> Integer
def after_status(code)
  case code
  when FIRST
    raise "first"
  when SECOND
    raise "second"
  end
  code
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn preserves_possible_nil_for_locals_read_from_ensure() {
    let result = check(
        r#"
class Client
  def close; end
end

def close_after_setup
  begin
    client = Client.new
  ensure
    client&.close
  end
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn infers_const_get_class_objects_from_literal_names() {
    let result = check(
        r#"
module Namespace
  class Thing
  end
end

T.reveal_type(Namespace.const_get("Thing"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `Class[Namespace::Thing]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn resolves_class_object_calls_through_class_and_module() {
    let result = check(
        r#"
class Module
  def inherited_module_method
  end
end

class Class < Module
end

class Example
end

Example.inherited_module_method
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn infers_array_to_h_key_and_value_types_from_block_pairs() {
    let result = check(
        r#"
class Entry
  #: -> String
  def key
    "entry"
  end
end

entries = [Entry.new]
T.reveal_type(entries.to_h { |entry| [entry.key, entry] })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Hash[String, Entry]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_set_element_types_through_set_difference() {
    let result = check(
        r#"
class Set
end

left = T.let(Set.new, T::Set[String])
right = T.let(Set.new, T::Set[String])
T.reveal_type(left - right)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Set[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_parser_source_coordinates_as_integers() {
    let result = check(
        r#"
module Parser
  module Source
    class Map
    end
  end
end

location = Parser::Source::Map.new
T.reveal_type(location.line)
T.reveal_type(location.column)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let integer_reveals = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.message.contains("Revealed type: `Integer`"))
        .count();
    assert_eq!(integer_reveals, 2, "{:?}", result.diagnostics);
}

#[test]
fn preserves_hash_pair_types_through_sort_and_to_h() {
    let result = check(
        r#"
values = {"a" => 1, "b" => 2}
sorted = values.sort
T.reveal_type(sorted)
T.reveal_type(sorted.to_h)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[[String, Integer]]`")
        }),
        "{:?}",
        result.diagnostics
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Hash[String, Integer]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_string_spaceship_comparison() {
    let result = check(
        r#"
T.reveal_type("a" <=> "b")
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Integer`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn propagates_namespaced_struct_fields_through_method_returns() {
    let result = check(
        r#"
class Package
end

module Discovery
  ConstantContext = Struct.new(:name, :package)

  #: (Package package) -> Discovery::ConstantContext
  def self.build(package)
    ConstantContext.new("constant", package)
  end
end

T.reveal_type(Discovery.build(Package.new).name)
T.reveal_type(Discovery.build(Package.new).package)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let messages = result
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        messages
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{messages:?}"
    );
    assert!(
        messages
            .iter()
            .any(|message| message.contains("Revealed type: `Package`")),
        "{messages:?}"
    );
}

#[test]
fn models_hash_predicate_blocks() {
    let result = check(
        r#"
values = {"a" => 1}
T.reveal_type(values.any? { |key, value| key == "a" && value == 1 })
T.reveal_type(values.all? { |key, value| key == "a" && value == 1 })
T.reveal_type(values.none? { |key, value| key == "b" && value == 2 })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let boolean_reveals = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.message.contains("Revealed type: `T::Boolean`"))
        .count();
    assert_eq!(boolean_reveals, 3, "{:?}", result.diagnostics);
}

#[test]
fn models_yaml_serialization_as_string() {
    let result = check(
        r#"
T.reveal_type({"a" => 1}.to_yaml)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_receiver_type_through_tap() {
    let result = check(
        r#"
T.reveal_type("value".tap { |value| value.length })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn evaluates_set_predicate_blocks() {
    let result = check(
        r#"
values = T.let(Set.new([1]), T::Set[Integer])
T.reveal_type(values.any? { |value| value > 0 })
T.reveal_type(values.all? { |value| value > 0 })
T.reveal_type(values.none? { |value| value < 0 })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let boolean_reveals = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.message.contains("Revealed type: `T::Boolean`"))
        .count();
    assert_eq!(boolean_reveals, 3, "{:?}", result.diagnostics);
}

#[test]
fn narrows_untyped_values_after_self_class_checks() {
    let result = check(
        r#"
class Package
  attr_reader :name

  #: (untyped other) -> String
  def other_name(other)
    return "" unless other.is_a?(self.class)
    T.reveal_type(other)
    other.name
  end
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `Package`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_typed_enumerator_map_results() {
    let result = check(
        r#"
values = T.let(T.unsafe(nil), T::Enumerator[Integer])
T.reveal_type(values.map { |value| value.to_s })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Array[String]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_each_with_object_array_types_through_prepend() {
    let result = check(
        r#"
values = [1].each_with_object([]) { |value, names| names.prepend(value.to_s) }
T.reveal_type(values)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Array[String]`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_each_with_object_nested_tuple_types_through_append() {
    let result = check(
        r#"
values = T.let(T.unsafe(nil), T::Array[[String, Object]])
result = values.each_with_object([]) do |(package, dependencies), invalid_packages|
  invalid_dependencies = if dependencies.is_a?(Array)
    dependency_values = dependencies #: as Array[Object]
    dependency_values.filter { |path| path.nil? }
  else
    [] #: as Array[Object]
  end
  T.reveal_type(package)
  T.reveal_type(dependencies)
  T.reveal_type(invalid_dependencies)
  invalid_packages << [package, invalid_dependencies] if invalid_dependencies.any?
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    for expected in [
        "Revealed type: `String`",
        "Revealed type: `Object`",
        "Revealed type: `T::Array[Object]`",
    ] {
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "missing {expected} in {:?}",
            result.diagnostics
        );
    }
}

#[test]
fn traverses_option_parser_configuration_blocks_with_option_types() {
    let result = check(
        r#"
OptionParser.new do |parser|
  parser.on("--name", String) { |name| T.reveal_type(name) }
  parser.on("--names", Array) { |names| T.reveal_type(names) }
  parser.on("--parallel", TrueClass) { |parallel| T.reveal_type(parallel) }
end
T.reveal_type(OptionParser.new)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    for expected in [
        "Revealed type: `String`",
        "Revealed type: `T::Array[String]`",
        "Revealed type: `T::Boolean`",
        "Revealed type: `OptionParser`",
    ] {
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "missing {expected} in {:?}",
            result.diagnostics
        );
    }
}

#[test]
fn infers_option_parser_parse_as_remaining_arguments() {
    let result = check(
        r#"
T.reveal_type(OptionParser.new.parse!(["--name", "value"]))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T::Array[String]`")),
        "missing Array[String] reveal in {:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_remaining_literal_expression_types() {
    let result = check(
        r#"
T.reveal_type(1r)
T.reveal_type(1i)
T.reveal_type(:"foo#{1}")
T.reveal_type(`echo hi`)
T.reveal_type(`echo #{1}`)
T.reveal_type(~ /text/)
flag = if true .. false
  true
else
  false
end
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
    for expected in [
        "Revealed type: `Rational`",
        "Revealed type: `Complex`",
        "Revealed type: `Symbol`",
        "Revealed type: `String`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T::Boolean`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
}

#[test]
fn infers_implicit_block_parameters() {
    let result = check(
        r#"
T.reveal_type([1].map { it + 1 })
T.reveal_type([1].map { _1 + 1 })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let arrays = result
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic
                    .message
                    .contains("Revealed type: `T::Array[Integer]`")
        })
        .count();
    assert_eq!(arrays, 2, "{:?}", result.diagnostics);
}

#[test]
fn propagates_inferred_block_returns_through_block_parameters() {
    let result = check(
        r#"
def apply(&block)
  block.call(1)
end

T.reveal_type(apply { |value| value.to_s })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `String`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn joins_all_arguments_into_rest_parameters() {
    let result = check(
        r#"
def first(*values)
  T.reveal_type(values)
  values[0]
end

def tail(head, *values)
  T.reveal_type(values)
  values[0]
end

T.reveal_type(first(1, "x"))
T.reveal_type(tail(0, 1, "x"))
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
            .filter(|message| {
                message.contains("Revealed type: `T::Array[T.any(Integer, String)]`")
            })
            .count(),
        2,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| {
                message.contains("Revealed type: `T.any(Integer, NilClass, String)`")
            })
            .count(),
        2,
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
fn models_blockless_collection_enumerators() {
    let result = check(
        r#"
values = [1, 2, 3]
hash = {"answer" => 1}

T.reveal_type(values.each)
T.reveal_type(values.map)
T.reveal_type(values.each_with_index)
T.reveal_type(values.select)
T.reveal_type(values.delete_if)
T.reveal_type(hash.each)
T.reveal_type(hash.transform_keys)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let enumerators = result
        .diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `Enumerator`")
        })
        .count();
    assert_eq!(enumerators, 7, "{:?}", result.diagnostics);
}

#[test]
fn models_array_delete_if_types() {
    let result = check(
        r#"
values = [1, 2, 3]

T.reveal_type(values.delete_if { |value| value.even? })
T.reveal_type(values.delete_if)
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
            .any(|message| message.contains("Revealed type: `T::Array[Integer]`")),
        "{notes:?}"
    );
    assert!(
        notes
            .iter()
            .any(|message| message.contains("Revealed type: `Enumerator`")),
        "{notes:?}"
    );
}

#[test]
fn preserves_more_array_method_types() {
    let result = check(
        r#"
values = [1, 2]

T.reveal_type(values.map! { |value| value.to_s })
T.reveal_type(values.sort_by { |value| -value })
T.reveal_type(values.product(["text"]))
T.reveal_type(values.sample)
T.reveal_type(values.sample(1))
T.reveal_type(values.min)
T.reveal_type(values.min_by { |value| value })
T.reveal_type(values.values_at(0))
T.reveal_type(values.pack("C*"))
T.reveal_type(values.combination(1))
T.reveal_type(values.shift)
T.reveal_type(values.pop(1))
T.reveal_type(values.fill(0))
T.reveal_type(values.replace([3]))
T.reveal_type(values.select! { |value| value.even? })
T.reveal_type(values.uniq!)
T.reveal_type(values.bsearch { |value| value > 0 })
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
        "Revealed type: `T::Array[[Integer, String]]`",
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T::Array[Integer]`",
        "Revealed type: `String`",
        "Revealed type: `Enumerator`",
        "Revealed type: `T.nilable(T::Array[Integer])`",
    ] {
        assert!(
            notes.iter().any(|message| message.contains(expected)),
            "missing {expected} in {notes:?}"
        );
    }
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
T.reveal_type(hash.fetch_values("answer"))
T.reveal_type(hash.dig("answer"))
T.reveal_type(hash.slice("answer"))
T.reveal_type(hash.except("answer"))
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
        "Revealed type: `T.nilable(Integer)`",
        "Revealed type: `T::Hash[String, Integer]`",
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
fn tracks_nonlocal_compound_assignments() {
    let result = check(
        r#"
$total = 1
$total += 2.0

TOTAL = 1
TOTAL += 2.0

class Counter
  @@total = 1
  @@total += 2.0

  def initialize
    @total = 1
    @total += 2.0
    @ready = true
    @ready &&= "yes"
  end

  def total
    @total
  end

  def ready
    @ready
  end

  def self.class_total
    @@total
  end
end

T.reveal_type($total)
T.reveal_type(TOTAL)
T.reveal_type(Counter.new.total)
T.reveal_type(Counter.new.ready)
T.reveal_type(Counter.class_total)
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
            .filter(|message| message.contains("Revealed type: `T.any(Float, Integer)`"))
            .count(),
        4,
        "{notes:?}"
    );
    assert_eq!(
        notes
            .iter()
            .filter(|message| message.contains("Revealed type: `T.any(String, TrueClass)`"))
            .count(),
        1,
        "{notes:?}"
    );
    assert!(
        !notes.iter().any(|message| message.contains("T.untyped")),
        "{notes:?}"
    );
}

#[test]
fn preserves_index_assignment_results() {
    let result = check(
        r#"
values = [1]
hash = {"answer" => 1}

T.reveal_type(values[0] = 2.0)
T.reveal_type(hash["other"] = "text")
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
            .any(|message| message.contains("Revealed type: `Float`")),
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
fn preserves_index_compound_assignment_results() {
    let result = check(
        r#"
values = [1]
hash = {"answer" => 1}

T.reveal_type(values[0] += 2.0)
T.reveal_type(hash["answer"] += 2.0)
T.reveal_type(values[0] &&= "updated")
T.reveal_type(hash["missing"] ||= "fallback")
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
        2,
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
fn infers_type_parameters_across_typed_rest_arguments() {
    let result = check(
        r#"
extend T::Sig

sig { type_parameters(:U).params(values: T.type_parameter(:U)).returns(T.type_parameter(:U)) }
def first(*values)
  T.must(values[0])
end

T.reveal_type(first(1, "value"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T.any(Integer, String)`")
        }),
        "{:?}",
        result.diagnostics
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
fn specializes_rbs_generic_type_members() {
    let result = check(
        r#"
class Poset
  extend T::Generic
  E = type_member

  #: (E from, E to) -> bool
  def edge?(from, to)
    true
  end
end

class Model
  #: -> Poset[Symbol]
  def hierarchy
    Poset.new
  end
end

Model.new.hierarchy.edge?(:first, :second)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
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
    assert_eq!(rest.rest_index, Some(1));
}

#[test]
fn tracks_optional_rbs_blocks() {
    let signature = typey::signature::parse_rbs_signature(
        "(String value) ?{ (String value) -> void } -> String",
    )
    .unwrap();
    assert_eq!(
        signature.block,
        Some(Type::union([
            Type::Nil,
            Type::Proc(vec![Type::String], Box::new(Type::Nil)),
        ]))
    );
}

#[test]
fn collects_optional_rbs_blocks_on_singleton_methods() {
    let source = "#: (String value) ?{ (String value) -> void } -> String\ndef self.call(value, &block)\nend\n";
    let annotations = typey::signature::collect(source);
    assert_eq!(
        annotations.methods["call"].block,
        Some(Type::union([
            Type::Nil,
            Type::Proc(vec![Type::String], Box::new(Type::Nil)),
        ]))
    );
}

#[test]
fn collects_optional_rbs_blocks_by_ast_offset() {
    let source = "#: (String value) ?{ (String value) -> void } -> String\ndef self.call(value, &block)\nend\n";
    let parsed = ruby_prism::parse(source.as_bytes());
    let annotations = typey::signature::collect_for_ast(source, &parsed.node());
    assert_eq!(annotations.method_annotations.len(), 1);
    let signature = annotations
        .method_annotations
        .values()
        .next()
        .and_then(|signatures| signatures.first())
        .expect("singleton method signature");
    assert!(signature.block.is_some(), "{signature:?}");
}

#[test]
fn tracks_rbs_method_type_parameters_for_generic_arguments() {
    let signature = typey::signature::parse_rbs_signature("[T] (Class[T] value) -> void")
        .expect("signature parses");
    assert_eq!(signature.type_parameters, vec!["T"]);
    assert_eq!(
        signature.params,
        vec![Type::Named(
            "Class".to_owned(),
            vec![Type::TypeVar("T".to_owned())]
        )]
    );

    let result = check(
        r#"
class Node
end

#: [T] (Class[T] value) -> void
def accept(value)
end

accept(Node)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
}

#[test]
fn propagates_rbs_block_parameter_types_and_method_type_parameters() {
    let signature = typey::signature::parse_rbs_signature(
        "[T] (Class[T] arg_type) { (T arg) -> void } -> void",
    )
    .expect("signature parses");
    assert_eq!(
        signature.block,
        Some(Type::Proc(
            vec![Type::TypeVar("T".to_owned())],
            Box::new(Type::Nil)
        ))
    );

    let result = check(
        r#"
#: [T] (Class[T] arg_type) { (T arg) -> void } -> void
def each_arg(arg_type, &block)
  yield(T.unsafe(nil)) if true
end

each_arg(Integer) do |arg|
  T.reveal_type(arg)
  nil
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `Integer`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_method_type_parameters_from_block_returns() {
    let result = check(
        r#"
#: [U] () { (Integer) -> U } -> Array[U]
def collect
  [1].map { |value| yield(value) }
end

T.reveal_type(collect { |value| value.to_s })
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic
                    .message
                    .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn typed_false_suppresses_type_errors_but_keeps_syntax_errors() {
    let semantic = check(
        "# typed: false\n\nT.let(\"wrong\", Integer)\n",
        CheckerConfig::default(),
    );
    assert!(
        semantic.diagnostics.is_empty(),
        "{:?}",
        semantic.diagnostics
    );

    let syntax = check(
        "# typed: false\n\ndef broken(\n  this is not valid Ruby\n",
        CheckerConfig::default(),
    );
    assert!(
        !syntax.diagnostics.is_empty(),
        "syntax error was suppressed"
    );
}

#[test]
fn unsigiled_sources_default_to_typed_true() {
    let result = check(
        "def opaque(value)\n  value\nend\nT.let(\"wrong\", Integer)\n",
        CheckerConfig::default(),
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Error
                && diagnostic
                    .message
                    .contains("Expected `Integer`, but found `String`")
        }),
        "{:?}",
        result.diagnostics
    );
    assert!(!result.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("insufficient inferred type information")
    }));
}

#[test]
fn reports_interface_annotations_only_on_preceding_classes() {
    let result = check(
        "# @interface\nclass Invalid\nend\n\nclass Valid\nend\n\n# @interface\nclass AnotherInvalid\nend\n",
        CheckerConfig::default(),
    );
    let errors = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 2, "{errors:?}");
    assert!(errors
        .iter()
        .all(|diagnostic| diagnostic.message.contains("Classes can't be interfaces")));
}

#[test]
fn strict_mode_accepts_methods_with_concrete_inferred_types() {
    let result = check(
        r#"# typed: strict

def add(left, right)
  left + right
end

T.reveal_type(add(1, 2))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Note
                && diagnostic.message.contains("Revealed type: `Integer`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn strict_mode_reports_unresolved_inference_gaps() {
    let result = check(
        "# typed: strict\n\ndef opaque(value)\n  value\nend\n",
        CheckerConfig::default(),
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Error
                && diagnostic
                    .message
                    .contains("insufficient inferred type information")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn inferred_types_mark_send_nodes() {
    let source = r#"# typed: strict

class Parent
  def render
    nil
  end
end

class Child < Parent
  def render
    yield("value")
    super
  end
end

"text".upcase
"#;
    let result = check(source, CheckerConfig::default());
    let sends = result
        .types
        .iter()
        .filter(|inferred| inferred.is_send)
        .map(|inferred| &source[inferred.start..inferred.end])
        .collect::<Vec<_>>();

    assert!(sends.iter().any(|send| send.contains("yield")));
    assert!(sends.iter().any(|send| send.trim() == "super"));
    assert!(sends.iter().any(|send| send.contains("upcase")));
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
fn preserves_string_types_through_active_support_inflections() {
    let result = check(
        r#"
T.reveal_type("file".pluralize)
T.reveal_type("offense".pluralize)
T.reveal_type("name".underscore)
T.reveal_type("posts".classify)
T.reveal_type("  message  ".squish)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message.contains("Revealed type: `String`"))
            .count(),
        5,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_inflector_classify_return_type() {
    let result = check(
        r#"
module ActiveSupport
  module Inflector
  end
end

T.reveal_type(ActiveSupport::Inflector.classify("posts"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_module_registration_calls() {
    let result = check(
        r#"
module Registry
  VALUE = 1

  def self.configure
    private_constant :VALUE
    autoload :Child, "child"
  end
end

T.reveal_type(Registry.configure)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("Revealed type: `NilClass`")
                || diagnostic.message.contains("Revealed type: `nil`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_dynamic_const_get_as_an_object() {
    let result = check(
        r#"
module Registry
  VALUE = 1

  #: (String) -> Object
  def self.lookup(name)
    const_get(name)
  end
end

T.reveal_type(Registry.lookup("VALUE"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `Object`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_extended_module_autoload_as_nil() {
    let result = check(
        r#"
module ActiveSupport
  module Autoload
    def autoload(const_name, path = nil)
      T.unsafe(nil)
    end
  end
end

module Registry
  extend ActiveSupport::Autoload
  T.reveal_type(autoload(:Child, "child"))
end
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `NilClass`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_yaml_dump_without_io_as_a_string() {
    let result = check(
        r#"
module Psych
end

T.reveal_type(Psych.dump({"key" => "value"}))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );

    let result = check(
        r#"
T.reveal_type(YAML.dump({"key" => "value"}))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("Revealed type: `String`")),
        "{:?}",
        result.diagnostics
    );

    let result = check(
        r#"
T.reveal_type(YAML.load_file("config.yml"))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("Revealed type: `T.nilable(Object)`")),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn narrows_ast_nodes_after_string_predicates() {
    let result = check(
        r#"
module NodeHelpers
  #: (AST::Node) -> bool
  def self.string?(node)
    true
  end

  #: (AST::Node) -> (String | Symbol)
  def self.literal_value(node)
    "value"
  end
end

module AST
  class Node
  end
end

def extract(node)
  return unless NodeHelpers.string?(node)

  NodeHelpers.literal_value(node)
end

T.reveal_type(extract(AST::Node.new))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T.nilable(String)`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn inherits_ivar_types_from_included_modules() {
    let result = check(
        r#"
class Files
  #: -> Array[String]
  def files
    ["file.rb"]
  end
end

module UsesFiles
  #: (Files) -> void
  def initialize(files)
    @files = files
  end
end

class Command
  include UsesFiles

  def files
    @files.files
  end
end

T.reveal_type(Command.new(Files.new).files)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_each_with_object_accumulator_types() {
    let result = check(
        r#"
values = [1].each_with_object(["seed"]) do |value, strings|
  strings << value.to_s
end

T.reveal_type(values)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_each_with_object_accumulator_types_for_typed_arrays() {
    let result = check(
        r#"
#: (Array[Integer]) -> Array[String]
def collect_strings(values)
  values.each_with_object(["seed"]) do |value, strings|
    strings << value.to_s
  end
end

T.reveal_type(collect_strings([1]))
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_empty_each_with_object_accumulators_from_block_writes() {
    let result = check(
        r#"
values = [1] #: Array[Integer]
strings = values.each_with_object([]) do |value, output|
  output << value.to_s
end

T.reveal_type(strings)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_namespaced_classes_that_shadow_primitives() {
    let result = check(
        r#"
module Outer
  class Symbol
  end

  class Registry
    def build
      Symbol.new
    end
  end
end

T.reveal_type(Outer::Registry.new.build)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(result.diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("Revealed type: `Outer::Symbol`")
    }));
}

#[test]
fn resolves_instance_methods_after_implicit_class_construction() {
    let result = check(
        r#"
class Generator
  class << self
    def build
      T.reveal_type(new.generate)
    end
  end

  def generate
    "generated"
  end
end

Generator.build
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
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

#[test]
fn infers_struct_new_field_types() {
    let result = check(
        r#"
Context = Struct.new(:name, :count)
context = Context.new("ready", 3)

T.reveal_type(context.name)
T.reveal_type(context.count)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let messages = result
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        messages
            .iter()
            .any(|message| message.contains("Revealed type: `String`")),
        "{messages:?}"
    );
    assert!(
        messages
            .iter()
            .any(|message| message.contains("Revealed type: `Integer`")),
        "{messages:?}"
    );
}

#[test]
fn models_struct_new_as_a_generated_class() {
    let mut files = load_workspace_paths(&builtin_rbi_paths().expect("vendored RBIs load"))
        .expect("vendored RBIs load");
    files.push(WorkspaceFile::new(
        "struct_constructor.rb",
        "# typed: true\nT.reveal_type(Struct.new(:name))\n",
    ));
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|diagnostic| {
                diagnostic
                    .diagnostic
                    .message
                    .contains("Revealed type: `Class[Struct]`")
            })
            .count(),
        1,
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_array_coercions_from_scalar_types() {
    let result = check(
        r#"
value = "glob"
values = Array(value)

T.reveal_type(values)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_env_lookup_as_nilable_string() {
    let result = check(
        r#"
key = "TYPEY_TEST_ENV"
value = ENV[key]

T.reveal_type(value)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T.nilable(String)`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_dir_as_string() {
    let result = check(
        r#"
path = __dir__

T.reveal_type(path)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn resolves_methods_from_required_ancestors() {
    let result = check(
        r#"
class Parent
  #: -> String
  def value
    "parent"
  end
end

# @requires_ancestor: Parent
module UsesParent
  def read_value
    value
  end
end

class Child
  include UsesParent
end

T.reveal_type(Child.new.read_value)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `String`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_enum_for_without_a_block() {
    let result = check(
        r#"
enumerator = enum_for(:each)

T.reveal_type(enumerator)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Enumerator`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_binding_return_type() {
    let result = check(
        r#"
current_binding = binding

T.reveal_type(current_binding)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Revealed type: `Binding`") }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_kernel_gem_return_type() {
    let result = check(
        r#"
specification = gem("json")

T.reveal_type(specification)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `Gem::Specification`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn infers_empty_each_with_object_hash_accumulators() {
    let result = check(
        r#"
entries = [1].each_with_object({}) do |value, output|
  output[value.to_s] = value
end

T.reveal_type(entries)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Hash[String, Integer]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn preserves_hash_value_types_through_empty_fetch_defaults() {
    let result = check(
        r#"
entries = {} #: Hash[String, Array[String]]
entries["files"] = ["one.rb"]
files = entries.fetch("files", [])

T.reveal_type(files)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `T::Array[String]`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn models_active_support_inflections() {
    let result = check(
        r#"
inflections = ActiveSupport::Inflector.inflections

T.reveal_type(inflections)
"#,
        CheckerConfig::default(),
    );
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("Revealed type: `ActiveSupport::Inflector::Inflections`")
        }),
        "{:?}",
        result.diagnostics
    );
}

#[test]
fn records_compound_assignments_as_send_sites() {
    let source = r#"
class Example
  def update(value)
    local = 1
    local += value
    @instance += value
    @@class_var += value
    $global += value
    CONSTANT += value
    self.value += value
    values[0] += value
  end
end
"#;
    let result = check(source, CheckerConfig::default());
    let send_count = result
        .types
        .iter()
        .filter(|inferred| inferred.is_send)
        .count();
    assert!(
        send_count >= 8,
        "expected compound assignment send sites, got {send_count}"
    );
}

#[test]
fn evaluates_multi_assignment_rhs_calls() {
    let source = r#"
def build
  [1, 2]
end

first, second = build
"#;
    let result = check(source, CheckerConfig::default());
    let build_start = source.rfind("build").expect("build call");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == build_start && inferred.end == build_start + 5
    }));
}

#[test]
fn evaluates_interpolation_expression_calls() {
    let source = r#"
name = "gem"
message = "missing #{name.inspect}"
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("name.inspect").expect("interpolation send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 12
    }));
}

#[test]
fn evaluates_parameter_default_calls() {
    let source = r#"
def build(timestamp: Time.now.utc, counts: Hash.new(0))
  [timestamp, counts]
end
"#;
    let result = check(source, CheckerConfig::default());
    for call in ["Time.now", "Time.now.utc", "Hash.new(0)"] {
        let send_start = source.find(call).expect("default call");
        assert!(
            result.types.iter().any(|inferred| {
                inferred.is_send
                    && inferred.start == send_start
                    && inferred.end == send_start + call.len()
            }),
            "missing send {call:?}"
        );
    }
}

#[test]
fn evaluates_array_predicate_blocks() {
    let source = r#"
[1].any? { |value| value.to_s }
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("value.to_s").expect("predicate send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 10
    }));
}

#[test]
fn evaluates_string_transform_blocks() {
    let source = r#"
"x".gsub(/x/) { |match| match.upcase }
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("match.upcase").expect("transform send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 12
    }));
}

#[test]
fn evaluates_call_assignment_rhs_calls() {
    let source = r#"
class Box
  def value
    1
  end

  def value=(value)
    value
  end
end

box = Box.new
box.value += Time.now
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("Time.now").expect("compound RHS send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 8
    }));
}

#[test]
fn evaluates_collection_callback_variants() {
    let source = r#"
{ key: 1 }.map { |_key, value| value.to_s }
[1].reverse_each { |value| value.to_s }
"#;
    let result = check(source, CheckerConfig::default());
    let sends = source.match_indices("value.to_s").collect::<Vec<_>>();
    assert_eq!(sends.len(), 2);
    for (send_start, _) in sends {
        assert!(result.types.iter().any(|inferred| {
            inferred.is_send && inferred.start == send_start && inferred.end == send_start + 10
        }));
    }
}

#[test]
fn evaluates_sum_callbacks() {
    let source = r#"
values = [1, 2]
values.sum { |value| value.to_f }
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("value.to_f").expect("sum block send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 10
    }));
}

#[test]
fn preserves_unmatched_paths_for_literal_case_values() {
    let source = r#"
def inspect
  value = :unhandled
  case value
  when :handled
    return
  end
  value.to_s
end
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.find("value.to_s").expect("post-case send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 10
    }));
}

#[test]
fn traverses_blocks_on_unknown_receivers() {
    let source = r#"
value = T.unsafe([])
value.each { |item| item.to_s }
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.rfind("item.to_s").expect("block send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 9
    }));
}

#[test]
fn traverses_blocks_on_unknown_super_calls() {
    let source = r#"
class Parent
  def filter(value)
    T.noreturn
  end
end

class Child < Parent
  def filter
    super.select { |item| item.to_s }
  end
end
"#;
    let result = check(source, CheckerConfig::default());
    let send_start = source.rfind("item.to_s").expect("block send");
    assert!(result.types.iter().any(|inferred| {
        inferred.is_send && inferred.start == send_start && inferred.end == send_start + 9
    }));
}

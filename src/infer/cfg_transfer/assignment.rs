//! Owned CFG transfer for writes and iteration bindings.

use super::super::hash_shape::HashShape;
use super::super::{ivar_refinement_key, Analyzer, Environment, SourceSite};
use super::globals::cfg_global_refinement_key;
use crate::cfg;
use crate::hir;
use crate::types::Type;

pub(super) fn hash_shape_key(analyzer: &Analyzer<'_>, place: &cfg::Place) -> Option<String> {
    match place {
        cfg::Place::Local(local) => analyzer
            .program
            .hir_program
            .local_name(*local)
            .map(|name| format!("\u{1}local:{}", name.as_str())),
        cfg::Place::InstanceVariable(name) => Some(ivar_refinement_key(name.as_str())),
        cfg::Place::ClassVariable(name) => Some(format!("\u{1}classvar:{}", name.as_str())),
        cfg::Place::Global(name) => Some(cfg_global_refinement_key(name.as_str())),
        cfg::Place::Constant(path) => Some(format!("\u{1}constant:{}", path.as_str())),
    }
}

pub(super) fn hash_shape_key_for_read(analyzer: &Analyzer<'_>, read: &hir::Read) -> Option<String> {
    match read {
        hir::Read::Local(local) => analyzer
            .program
            .hir_program
            .local_name(*local)
            .map(|name| format!("\u{1}local:{}", name.as_str())),
        hir::Read::InstanceVariable(name) => Some(ivar_refinement_key(name.as_str())),
        hir::Read::ClassVariable(name) => Some(format!("\u{1}classvar:{}", name.as_str())),
        hir::Read::Global(name) => Some(cfg_global_refinement_key(name.as_str())),
        hir::Read::Constant(path) => Some(format!("\u{1}constant:{}", path.as_str())),
        hir::Read::SelfValue
        | hir::Read::Numbered(_)
        | hir::Read::It
        | hir::Read::BackReference(_) => None,
    }
}

pub(super) fn transfer_write<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    place: &cfg::Place,
    expression: Option<hir::ExprId>,
    actual: Type,
    hash_shape: Option<HashShape>,
    logical: bool,
    environment: &mut Environment,
) -> Type {
    transfer_write_inner(
        analyzer,
        site,
        place,
        expression,
        actual,
        hash_shape,
        logical,
        environment,
        true,
    )
}

fn transfer_write_inner<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    place: &cfg::Place,
    expression: Option<hir::ExprId>,
    actual: Type,
    hash_shape: Option<HashShape>,
    logical: bool,
    environment: &mut Environment,
    apply_inline_assertion: bool,
) -> Type {
    let actual = match place {
        cfg::Place::Constant(path) => expression
            .and_then(|expression| {
                dynamic_struct_constant_type(analyzer, expression, path, environment)
            })
            .unwrap_or(actual),
        _ => actual,
    };
    match place {
        cfg::Place::Local(local) => {
            let name = analyzer
                .program
                .hir_program
                .local_name(*local)
                .map_or_else(String::new, |name| name.as_str().to_owned());
            let type_ = if apply_inline_assertion {
                analyzer.apply_inline_assertion_in_environment_at(site, actual, environment)
            } else {
                actual
            };
            let type_ = if logical {
                type_.without(&Type::Nil)
            } else {
                type_
            };
            environment.bind(&name, type_.clone());
            let empty_array = expression
                .and_then(|id| analyzer.program.hir_program.expression(id))
                .and_then(|expression| match &expression.kind {
                    hir::ExprKind::Assign { value, .. } => {
                        analyzer.program.hir_program.expression(*value)
                    }
                    hir::ExprKind::Array(_) => Some(expression),
                    _ => None,
                })
                .is_some_and(|expression| {
                    matches!(&expression.kind, hir::ExprKind::Array(elements) if elements.is_empty())
                });
            if empty_array && matches!(&type_, Type::Array(element) if element.is_any()) {
                environment.open_array_locals.insert(name.clone());
            }
            environment.set_hash_shape(format!("\u{1}local:{name}"), hash_shape);
            type_
        }
        cfg::Place::InstanceVariable(name) => {
            let name = name.as_str().to_owned();
            let type_ = if apply_inline_assertion {
                analyzer.apply_inline_assertion_in_environment_at(site, actual, environment)
            } else {
                actual
            };
            let type_ = if logical {
                type_.without(&Type::Nil)
            } else {
                type_
            };
            analyzer.observe_ivar(environment, name.clone(), &type_, false);
            let refinement = ivar_refinement_key(&name);
            environment.bind(&refinement, type_.clone());
            environment.set_hash_shape(refinement, hash_shape);
            type_
        }
        cfg::Place::ClassVariable(name) => {
            let type_ = if apply_inline_assertion {
                analyzer.apply_inline_assertion_at(site, actual)
            } else {
                actual
            };
            analyzer.observe_class_var(environment, name.as_str().to_owned(), &type_);
            environment.set_hash_shape(format!("\u{1}classvar:{}", name.as_str()), hash_shape);
            type_
        }
        cfg::Place::Global(name) => {
            let type_ = if apply_inline_assertion {
                analyzer.apply_inline_assertion_at(site, actual)
            } else {
                actual
            };
            environment.bind(cfg_global_refinement_key(name.as_str()), type_.clone());
            environment.set_hash_shape(cfg_global_refinement_key(name.as_str()), hash_shape);
            type_
        }
        cfg::Place::Constant(path) => {
            let type_ = if apply_inline_assertion {
                analyzer.apply_inline_assertion_at(site, actual)
            } else {
                actual
            };
            analyzer.observe_constant(environment, path.as_str().to_owned(), &type_);
            environment.set_hash_shape(format!("\u{1}constant:{}", path.as_str()), hash_shape);
            type_
        }
    }
}

pub(super) fn transfer_for_target<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    target: &hir::AssignTarget,
    element_type: Type,
    environment: &mut Environment,
) -> Option<Type> {
    transfer_for_target_inner(analyzer, site, target, element_type, environment, true)
}

/// Transfer a destructuring target without applying an assertion attached to
/// the complete RHS. An assertion such as `left, right = value #: as [...]`
/// describes `value`; applying it again to each projected element would
/// incorrectly replace every element with the tuple type.
pub(super) fn transfer_for_target_without_inline_assertion<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    target: &hir::AssignTarget,
    element_type: Type,
    environment: &mut Environment,
) -> Option<Type> {
    transfer_for_target_inner(analyzer, site, target, element_type, environment, false)
}

fn transfer_for_target_inner<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    target: &hir::AssignTarget,
    element_type: Type,
    environment: &mut Environment,
    apply_inline_assertion: bool,
) -> Option<Type> {
    let place = match target {
        hir::AssignTarget::Local(local) => cfg::Place::Local(*local),
        hir::AssignTarget::InstanceVariable(name) => cfg::Place::InstanceVariable(name.clone()),
        hir::AssignTarget::ClassVariable(name) => cfg::Place::ClassVariable(name.clone()),
        hir::AssignTarget::Global(name) => cfg::Place::Global(name.clone()),
        hir::AssignTarget::Constant(path) => cfg::Place::Constant(path.clone()),
        hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. } => return None,
    };
    let open_array = matches!(&element_type, Type::Array(element) if element.is_never());
    let result = transfer_write_inner(
        analyzer,
        site,
        &place,
        None,
        element_type,
        None,
        false,
        environment,
        apply_inline_assertion,
    );
    if open_array {
        if let hir::AssignTarget::Local(local) = target {
            if let Some(name) = analyzer.program.hir_program.local_name(*local) {
                environment
                    .open_array_locals
                    .insert(name.as_str().to_owned());
            }
        }
    }
    Some(result)
}

/// `Struct.new` returns a class object at runtime, but assigning that class to
/// a constant gives it a concrete nominal identity. The recursive evaluator
/// has historically applied that identity while evaluating the assignment;
/// keep the same rule in the owned CFG path using only HIR data.
fn dynamic_struct_constant_type<'src>(
    analyzer: &mut Analyzer<'src>,
    expression: hir::ExprId,
    path: &hir::ConstantPath,
    environment: &Environment,
) -> Option<Type> {
    let assignment = analyzer.program.hir_program.expression(expression)?;
    let hir::ExprKind::Assign { value, .. } = &assignment.kind else {
        return None;
    };
    let value = analyzer.program.hir_program.expression(*value)?;
    let hir::ExprKind::Call(call) = &value.kind else {
        return None;
    };
    if call.name.as_str() != "new" {
        return None;
    }
    let hir::Receiver::Explicit(receiver) = call.receiver else {
        return None;
    };
    let receiver = analyzer.program.hir_program.expression(receiver)?;
    let hir::ExprKind::Read(hir::Read::Constant(receiver)) = &receiver.kind else {
        return None;
    };
    if receiver.as_str().trim_start_matches("::") != "Struct" {
        return None;
    }

    let owner = analyzer.constant_key(environment, path.as_str());
    let fields = call
        .arguments
        .iter()
        .filter_map(|argument| match argument {
            hir::Argument::Positional(value) => analyzer
                .program
                .hir_program
                .expression(*value)
                .and_then(|expression| match &expression.kind {
                    hir::ExprKind::Literal(hir::Literal::Symbol(name)) => Some(name.clone()),
                    _ => None,
                }),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !fields.is_empty() {
        analyzer
            .declarations
            .struct_fields
            .entry(owner.clone())
            .or_insert(fields);
    }
    Some(Type::named(owner))
}

pub(super) fn transfer_multi_write<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    expression: Option<hir::ExprId>,
    value_type: Type,
    lefts: &[hir::AssignTarget],
    rest: Option<&hir::AssignTarget>,
    rights: &[hir::AssignTarget],
    environment: &mut Environment,
) -> Option<Type> {
    let known_length = match &value_type {
        Type::Tuple(elements) => Some(elements.len()),
        _ => None,
    };
    for (index, target) in lefts.iter().enumerate() {
        let element_type = analyzer.multi_assignment_element_type(&value_type, index, known_length);
        transfer_for_target_without_inline_assertion(
            analyzer,
            site,
            target,
            element_type,
            environment,
        )?;
        if is_empty_array_element(analyzer, expression, index) {
            mark_open_array_target(analyzer, target, environment);
        }
    }
    if let Some(target) = rest {
        let element_type = analyzer.array_element_type(&value_type);
        transfer_for_target_without_inline_assertion(
            analyzer,
            site,
            target,
            Type::union([Type::Nil, Type::Array(Box::new(element_type))]),
            environment,
        )?;
    }
    let right_start = known_length
        .map(|length| lefts.len().max(length.saturating_sub(rights.len())))
        .unwrap_or(0);
    for (index, target) in rights.iter().enumerate() {
        let element_type =
            analyzer.multi_assignment_element_type(&value_type, right_start + index, known_length);
        transfer_for_target_without_inline_assertion(
            analyzer,
            site,
            target,
            element_type,
            environment,
        )?;
        if is_empty_array_element(analyzer, expression, right_start + index) {
            mark_open_array_target(analyzer, target, environment);
        }
    }
    Some(value_type)
}

fn is_empty_array_element(
    analyzer: &Analyzer<'_>,
    expression: Option<hir::ExprId>,
    index: usize,
) -> bool {
    let Some(expression) = expression.and_then(|id| analyzer.program.hir_program.expression(id))
    else {
        return false;
    };
    let hir::ExprKind::MultiAssign { value, .. } = &expression.kind else {
        return false;
    };
    let Some(hir::Expr {
        kind: hir::ExprKind::Array(elements),
        ..
    }) = analyzer.program.hir_program.expression(*value)
    else {
        return false;
    };
    let Some(hir::ArrayElement::Value(value)) = elements.get(index) else {
        return false;
    };
    matches!(
        analyzer.program.hir_program.expression(*value),
        Some(hir::Expr {
            kind: hir::ExprKind::Array(elements),
            ..
        }) if elements.is_empty()
    )
}

fn mark_open_array_target(
    analyzer: &Analyzer<'_>,
    target: &hir::AssignTarget,
    environment: &mut Environment,
) {
    if let hir::AssignTarget::Local(local) = target {
        if let Some(name) = analyzer.program.hir_program.local_name(*local) {
            environment
                .open_array_locals
                .insert(name.as_str().to_owned());
        }
    }
}

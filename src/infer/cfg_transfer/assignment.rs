//! Owned CFG transfer for writes and iteration bindings.

use super::super::{ivar_refinement_key, Analyzer, Environment, SourceSite};
use super::globals::cfg_global_refinement_key;
use crate::cfg;
use crate::hir;
use crate::types::Type;

pub(super) fn transfer_write<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
    place: &cfg::Place,
    actual: Type,
    logical: bool,
    environment: &mut Environment,
) -> Type {
    match place {
        cfg::Place::Local(local) => {
            let name = analyzer
                .program
                .hir_program
                .local_name(*local)
                .map_or_else(String::new, |name| name.as_str().to_owned());
            let type_ =
                analyzer.apply_inline_assertion_in_environment_at(site, actual, environment);
            let type_ = if logical {
                type_.without(&Type::Nil)
            } else {
                type_
            };
            environment.bind(name, type_.clone());
            type_
        }
        cfg::Place::InstanceVariable(name) => {
            let name = name.as_str().to_owned();
            let type_ =
                analyzer.apply_inline_assertion_in_environment_at(site, actual, environment);
            let type_ = if logical {
                type_.without(&Type::Nil)
            } else {
                type_
            };
            analyzer.observe_ivar(environment, name.clone(), &type_, false);
            environment.bind(ivar_refinement_key(&name), type_.clone());
            type_
        }
        cfg::Place::ClassVariable(name) => {
            let type_ = analyzer.apply_inline_assertion_at(site, actual);
            analyzer.observe_class_var(environment, name.as_str().to_owned(), &type_);
            type_
        }
        cfg::Place::Global(name) => {
            let type_ = analyzer.apply_inline_assertion_at(site, actual);
            environment.bind(cfg_global_refinement_key(name.as_str()), type_.clone());
            type_
        }
        cfg::Place::Constant(path) => {
            let type_ = analyzer.apply_inline_assertion_at(site, actual);
            analyzer.observe_constant(environment, path.as_str().to_owned(), &type_);
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
    let place = match target {
        hir::AssignTarget::Local(local) => cfg::Place::Local(*local),
        hir::AssignTarget::InstanceVariable(name) => cfg::Place::InstanceVariable(name.clone()),
        hir::AssignTarget::ClassVariable(name) => cfg::Place::ClassVariable(name.clone()),
        hir::AssignTarget::Global(name) => cfg::Place::Global(name.clone()),
        hir::AssignTarget::Constant(path) => cfg::Place::Constant(path.clone()),
        hir::AssignTarget::Attribute { .. } | hir::AssignTarget::Index { .. } => return None,
    };
    Some(transfer_write(
        analyzer,
        site,
        &place,
        element_type,
        false,
        environment,
    ))
}

pub(super) fn transfer_multi_write<'src>(
    analyzer: &mut Analyzer<'src>,
    site: SourceSite,
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
        transfer_for_target(analyzer, site, target, element_type, environment)?;
    }
    if let Some(target) = rest {
        let element_type = analyzer.array_element_type(&value_type);
        transfer_for_target(
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
        transfer_for_target(analyzer, site, target, element_type, environment)?;
    }
    Some(value_type)
}

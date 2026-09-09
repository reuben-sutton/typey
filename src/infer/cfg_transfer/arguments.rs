//! Owned CFG call-argument materialization.

use super::super::{
    Analyzer, CallArguments, Environment, KeywordArgument, OwnedCallInput, SourceSite,
};
use crate::cfg;
use crate::hir;
use crate::types::Type;
use std::collections::HashMap;

#[derive(Clone, Debug)]
struct OwnedKeywordArgument {
    name: String,
    value_site: SourceSite,
    type_: Type,
}

/// Semantic call arguments produced from HIR and CFG values.
#[derive(Clone, Debug, Default)]
pub(super) struct OwnedCallArguments {
    argument_sites: Vec<SourceSite>,
    argument_types: Vec<Type>,
    argument_indices: Vec<usize>,
    positional_indices: Vec<usize>,
    positional_types: Vec<Type>,
    keyword_arguments: Vec<OwnedKeywordArgument>,
    keyword_hash_indices: Vec<usize>,
    has_keyword_splat: bool,
    has_dynamic_positional_splat: bool,
    dynamic_positional_splat_types: Vec<Type>,
    has_dynamic_keyword_splat: bool,
    has_unknown_positional_splat: bool,
    has_unknown_keyword_splat: bool,
    forwards_arguments: bool,
}

impl OwnedCallArguments {
    pub(super) fn into_call_arguments<'node>(self) -> CallArguments<'node> {
        let argument_sites = self.argument_sites;
        let keyword_arguments = self
            .keyword_arguments
            .into_iter()
            .map(|argument| KeywordArgument {
                name: argument.name,
                node: None,
                site: argument.value_site,
                type_: argument.type_,
            })
            .collect();
        CallArguments {
            argument_nodes: Vec::new(),
            argument_sites,
            argument_types: self.argument_types,
            argument_indices: self.argument_indices,
            positional_indices: self.positional_indices,
            positional_types: self.positional_types,
            keyword_arguments,
            keyword_hash_indices: self.keyword_hash_indices,
            has_keyword_splat: self.has_keyword_splat,
            has_dynamic_positional_splat: self.has_dynamic_positional_splat,
            dynamic_positional_splat_types: self.dynamic_positional_splat_types,
            has_dynamic_keyword_splat: self.has_dynamic_keyword_splat,
            has_unknown_positional_splat: self.has_unknown_positional_splat,
            has_unknown_keyword_splat: self.has_unknown_keyword_splat,
            forwards_arguments: self.forwards_arguments,
        }
    }
}

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_owned_hir_call_arguments(
        &mut self,
        input: &OwnedCallInput,
        call: &hir::Call,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
        environment: &Environment,
    ) -> Option<OwnedCallArguments> {
        if call
            .arguments
            .iter()
            .any(|argument| matches!(argument, hir::Argument::Forwarded))
        {
            if !call
                .arguments
                .iter()
                .all(|argument| matches!(argument, hir::Argument::Forwarded))
            {
                return None;
            }
            let method = environment.method_key.as_ref()?;
            let state = self.declarations.methods.get(method)?;
            let positional_types = state.call_signature().params;
            let mut call_arguments = OwnedCallArguments {
                argument_types: positional_types.clone(),
                positional_types,
                forwards_arguments: true,
                argument_sites: call
                    .argument_spans
                    .iter()
                    .copied()
                    .map(|span| SourceSite::from_span(span, None))
                    .collect(),
                ..OwnedCallArguments::default()
            };
            call_arguments.argument_indices = (0..call_arguments.argument_types.len()).collect();
            call_arguments.positional_indices = call_arguments.argument_indices.clone();
            return Some(call_arguments);
        }
        if call.argument_spans.len() != call.argument_groups.len() {
            return None;
        }
        let mut call_arguments = OwnedCallArguments::default();
        let mut operand_index = 0usize;
        let mut group_start = 0usize;
        for (argument_index, (group_end, span)) in call
            .argument_groups
            .iter()
            .zip(&call.argument_spans)
            .enumerate()
        {
            call_arguments
                .argument_sites
                .push(SourceSite::from_span(*span, None));
            let group = call.arguments.get(group_start..*group_end)?;
            if !group.is_empty()
                && group.iter().all(|argument| {
                    matches!(
                        argument,
                        hir::Argument::Keyword { .. } | hir::Argument::KeywordSplat(_)
                    )
                })
            {
                call_arguments.keyword_hash_indices.push(argument_index);
                let mut key = Type::Never;
                let mut value = Type::Never;
                for argument in group {
                    match argument {
                        hir::Argument::Keyword {
                            name,
                            name_span,
                            value: value_id,
                        } => {
                            let cfg::ArgumentOperand::Keyword {
                                name: operand_name,
                                value: cfg_value_id,
                            } = input.arguments.get(operand_index)?
                            else {
                                return None;
                            };
                            let type_ = values.get(cfg_value_id.0 as usize).cloned().flatten()?;
                            if name.as_str() != operand_name.as_str() {
                                return None;
                            }
                            key = key.join(&Type::Symbol);
                            value = value.join(&type_);
                            let name_site = SourceSite::from_span(*name_span, None);
                            let value_site =
                                self.program.hir_program.expression(*value_id).map(
                                    |expression| SourceSite::from_span(expression.span, None),
                                )?;
                            self.record_at(name_site, Type::Symbol, false, None);
                            call_arguments.keyword_arguments.push(OwnedKeywordArgument {
                                name: name.as_str().to_owned(),
                                value_site,
                                type_,
                            });
                        }
                        hir::Argument::KeywordSplat(_) => {
                            let cfg::ArgumentOperand::KeywordSplat(value_id) =
                                input.arguments.get(operand_index)?
                            else {
                                return None;
                            };
                            let type_ = values.get(value_id.0 as usize).cloned().flatten()?;
                            call_arguments.has_keyword_splat = true;
                            match type_ {
                                Type::Hash(splat_key, splat_value) => {
                                    key = key.join(&splat_key);
                                    value = value.join(&splat_value);
                                    call_arguments.has_dynamic_keyword_splat = true;
                                }
                                Type::Any => {
                                    key = Type::Any;
                                    value = Type::Any;
                                    call_arguments.has_unknown_keyword_splat = true;
                                }
                                _ => {
                                    key = Type::Any;
                                    value = Type::Any;
                                    call_arguments.has_dynamic_keyword_splat = true;
                                }
                            }
                        }
                        _ => return None,
                    }
                    operand_index += 1;
                }
                let key = if key.is_never() { Type::Any } else { key };
                let value = if value.is_never() { Type::Any } else { value };
                let site = SourceSite::from_span(*span, None);
                let hash_type = self
                    .apply_inline_assertion_at(site, Type::Hash(Box::new(key), Box::new(value)));
                let hash_type = self.record_at(site, hash_type, false, None);
                call_arguments.argument_types.push(hash_type);
                call_arguments.argument_indices.push(argument_index);
                group_start = *group_end;
                continue;
            }
            if group.len() != 1 {
                return None;
            }
            if let Some(cfg::ArgumentOperand::Splat(value)) = input.arguments.get(operand_index) {
                let type_ = values.get(value.0 as usize).cloned().flatten()?;
                if let Some(elements) = fixed_array_elements.get(value) {
                    for element in elements {
                        let type_ = values.get(element.0 as usize).cloned().flatten()?;
                        call_arguments.argument_types.push(type_.clone());
                        call_arguments.argument_indices.push(argument_index);
                        call_arguments.positional_indices.push(argument_index);
                        call_arguments.positional_types.push(type_);
                    }
                } else if let Type::Tuple(elements) = type_ {
                    for type_ in elements {
                        call_arguments.argument_types.push(type_.clone());
                        call_arguments.argument_indices.push(argument_index);
                        call_arguments.positional_indices.push(argument_index);
                        call_arguments.positional_types.push(type_);
                    }
                } else if type_.is_any() {
                    call_arguments.has_unknown_positional_splat = true;
                } else {
                    call_arguments.has_dynamic_positional_splat = true;
                    call_arguments.dynamic_positional_splat_types.push(type_);
                }
                operand_index += 1;
                group_start = *group_end;
                continue;
            }
            let Some(cfg::ArgumentOperand::Positional(value)) = input.arguments.get(operand_index)
            else {
                return None;
            };
            let type_ = values.get(value.0 as usize).cloned().flatten()?;
            call_arguments.argument_types.push(type_.clone());
            call_arguments.argument_indices.push(argument_index);
            call_arguments.positional_indices.push(argument_index);
            call_arguments.positional_types.push(type_);
            operand_index += 1;
            group_start = *group_end;
        }
        (group_start == call.arguments.len() && operand_index == input.arguments.len())
            .then_some(call_arguments)
    }

    /// Materialize call arguments for CFG operations synthesized by lowering,
    /// such as the `+` send inside `value += 1`. These operations have owned
    /// operand values but no HIR `Call` or parser argument node to bridge.
    pub(super) fn cfg_owned_call_arguments<'node>(
        &mut self,
        input: &OwnedCallInput,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
    ) -> Option<CallArguments<'node>> {
        let mut call_arguments = CallArguments::default();
        for (argument_index, argument) in input.arguments.iter().enumerate() {
            call_arguments.argument_sites.push(input.site);
            match argument {
                cfg::ArgumentOperand::Positional(value) => {
                    let type_ = values.get(value.0 as usize).cloned().flatten()?;
                    call_arguments.argument_types.push(type_.clone());
                    call_arguments.argument_indices.push(argument_index);
                    call_arguments.positional_indices.push(argument_index);
                    call_arguments.positional_types.push(type_);
                }
                cfg::ArgumentOperand::Splat(value) => {
                    let type_ = values.get(value.0 as usize).cloned().flatten()?;
                    if let Some(elements) = fixed_array_elements.get(value) {
                        for element in elements {
                            let type_ = values.get(element.0 as usize).cloned().flatten()?;
                            call_arguments.argument_types.push(type_.clone());
                            call_arguments.argument_indices.push(argument_index);
                            call_arguments.positional_indices.push(argument_index);
                            call_arguments.positional_types.push(type_);
                        }
                    } else if let Type::Tuple(elements) = type_ {
                        for type_ in elements {
                            call_arguments.argument_types.push(type_.clone());
                            call_arguments.argument_indices.push(argument_index);
                            call_arguments.positional_indices.push(argument_index);
                            call_arguments.positional_types.push(type_);
                        }
                    } else if type_.is_any() {
                        call_arguments.has_unknown_positional_splat = true;
                    } else {
                        call_arguments.has_dynamic_positional_splat = true;
                        call_arguments.dynamic_positional_splat_types.push(type_);
                    }
                }
                cfg::ArgumentOperand::Keyword { value, .. } => {
                    let type_ = values.get(value.0 as usize).cloned().flatten()?;
                    call_arguments.argument_types.push(type_);
                    call_arguments.argument_indices.push(argument_index);
                    call_arguments.keyword_hash_indices.push(argument_index);
                }
                cfg::ArgumentOperand::KeywordSplat(value) => {
                    let type_ = values.get(value.0 as usize).cloned().flatten()?;
                    call_arguments.has_keyword_splat = true;
                    match type_ {
                        Type::Hash(key, value) => {
                            call_arguments.has_dynamic_keyword_splat = true;
                            call_arguments.argument_types.push(Type::Hash(key, value));
                        }
                        Type::Any => {
                            call_arguments.has_unknown_keyword_splat = true;
                        }
                        _ => {
                            call_arguments.has_dynamic_keyword_splat = true;
                        }
                    }
                    call_arguments.argument_indices.push(argument_index);
                    call_arguments.keyword_hash_indices.push(argument_index);
                }
                cfg::ArgumentOperand::Forwarded => return None,
            }
        }
        Some(call_arguments)
    }
}

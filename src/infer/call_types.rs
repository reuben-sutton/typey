//! Owned shapes used at the boundary between Ruby call syntax and dispatch.
//!
//! The recursive evaluator still stores parser nodes on these shapes for
//! diagnostics and builtin hooks. Keeping the call vocabulary in its own
//! layer makes that dependency explicit and gives CFG transfer a stable place
//! to introduce source-owned call inputs.

use super::{proc_parts, Analyzer, Flow, MethodKey, OutcomeTypes, SourceSite};
use crate::cfg;
use crate::hir;
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::Node;
use std::collections::HashMap;

pub(super) struct CallSite<'a, 'node> {
    pub(super) argument_nodes: &'a [Node<'node>],
    pub(super) argument_types: &'a [Type],
    pub(super) block: Option<&'a Node<'node>>,
}

/// The owned semantic input consumed by CFG call transfer. Parser nodes are
/// deliberately absent; source nodes remain a separate compatibility adapter
/// for legacy diagnostic and builtin APIs.
#[derive(Clone, Debug)]
pub(super) struct OwnedCallInput {
    pub(super) site: SourceSite,
    pub(super) expression: Option<hir::ExprId>,
    pub(super) receiver: cfg::ReceiverOperand,
    pub(super) name: hir::Name,
    pub(super) arguments: Vec<cfg::ArgumentOperand>,
    pub(super) block: Option<cfg::BlockOperand>,
    pub(super) safe_navigation: bool,
}

impl OwnedCallInput {
    pub(super) fn from_operation(operation: &cfg::Operation) -> Option<Self> {
        let cfg::OperationKind::Call {
            receiver,
            name,
            arguments,
            block,
            safe_navigation,
        } = &operation.kind
        else {
            return None;
        };
        Some(Self {
            site: SourceSite::from_span(operation.span, operation.expression),
            expression: operation.expression,
            receiver: receiver.clone(),
            name: name.clone(),
            arguments: arguments.clone(),
            block: block.clone(),
            safe_navigation: *safe_navigation,
        })
    }
}

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_block_return_type<'node>(
        &mut self,
        input: &OwnedCallInput,
        block_node: Option<&Node<'node>>,
        key: &MethodKey,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<Type> {
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(_) => self.observe_block_call(
                key,
                block_node,
                signature,
                arguments,
                Some(receiver_type),
                environment,
            ),
            cfg::BlockOperand::Passed(value) => values
                .get(value.0 as usize)
                .and_then(Option::as_ref)
                .and_then(proc_parts)
                .map(|(_, result)| result.clone()),
        }
    }

    pub(super) fn cfg_call_arguments<'node>(
        &mut self,
        input: &OwnedCallInput,
        call: &hir::Call,
        node: &Node<'node>,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
        environment: &super::Environment,
    ) -> Option<CallArguments<'node>> {
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
            let mut call_arguments = CallArguments {
                argument_types: positional_types.clone(),
                positional_types,
                forwards_arguments: true,
                ..CallArguments::default()
            };
            call_arguments.argument_indices = (0..call_arguments.argument_types.len()).collect();
            call_arguments.positional_indices = call_arguments.argument_indices.clone();
            return Some(call_arguments);
        }
        let raw_argument_nodes = node
            .as_call_node()
            .and_then(|call| call.arguments())
            .or_else(|| {
                node.as_super_node()
                    .and_then(|super_node| super_node.arguments())
            })
            .or_else(|| {
                node.as_yield_node()
                    .and_then(|yield_node| yield_node.arguments())
            })
            .map(|arguments| arguments.arguments().into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        if raw_argument_nodes.len() != call.argument_groups.len() {
            return None;
        }
        let mut raw_argument_nodes = raw_argument_nodes.into_iter();
        let mut call_arguments = CallArguments::default();
        let mut operand_index = 0usize;
        let mut group_start = 0usize;
        for (argument_index, (group_end, span)) in call
            .argument_groups
            .iter()
            .zip(&call.argument_spans)
            .enumerate()
        {
            let argument_node = raw_argument_nodes.next()?;
            debug_assert_eq!(
                crate::prism::span(&argument_node),
                (span.start as usize, span.end as usize)
            );
            let group = call.arguments.get(group_start..*group_end)?;
            if !group.is_empty()
                && group.iter().all(|argument| {
                    matches!(
                        argument,
                        hir::Argument::Keyword { .. } | hir::Argument::KeywordSplat(_)
                    )
                })
            {
                let keyword_entries = argument_node
                    .as_keyword_hash_node()?
                    .elements()
                    .into_iter()
                    .map(|element| {
                        if let Some(assoc) = element.as_assoc_node() {
                            self.record(&assoc.key(), Type::Symbol);
                            Some((true, assoc.value()))
                        } else if let Some(splat) = element.as_assoc_splat_node() {
                            Some((false, splat.value()?))
                        } else {
                            None
                        }
                    })
                    .collect::<Option<Vec<_>>>()?;
                let mut keyword_entries = keyword_entries.into_iter();
                let mut key = Type::Never;
                let mut value = Type::Never;
                let mut keyword_arguments = Vec::with_capacity(group.len());
                for argument in group {
                    let (pair, value_node) = keyword_entries.next()?;
                    match argument {
                        hir::Argument::Keyword { name, value: _ } if pair => {
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
                            keyword_arguments.push(KeywordArgument {
                                name: name.as_str().to_owned(),
                                node: value_node,
                                type_,
                            });
                        }
                        hir::Argument::KeywordSplat(_) if !pair => {
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
                if keyword_entries.next().is_some() {
                    return None;
                }
                let key = if key.is_never() { Type::Any } else { key };
                let value = if value.is_never() { Type::Any } else { value };
                let hash_type = self.apply_inline_assertion(
                    &argument_node,
                    Type::Hash(Box::new(key), Box::new(value)),
                );
                self.record(&argument_node, hash_type.clone());
                call_arguments.argument_nodes.push(argument_node);
                call_arguments.argument_types.push(hash_type);
                call_arguments.argument_indices.push(argument_index);
                call_arguments.keyword_arguments.extend(keyword_arguments);
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
                call_arguments.argument_nodes.push(argument_node);
                operand_index += 1;
                group_start = *group_end;
                continue;
            }
            let Some(cfg::ArgumentOperand::Positional(value)) = input.arguments.get(operand_index)
            else {
                return None;
            };
            let type_ = values.get(value.0 as usize).cloned().flatten()?;
            call_arguments.argument_nodes.push(argument_node);
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
}

pub(super) enum CallArgumentInput<'node> {
    Forwarded {
        node: Node<'node>,
    },
    Positional {
        node: Node<'node>,
    },
    Splat {
        node: Node<'node>,
        expression: Option<Node<'node>>,
    },
    KeywordHash {
        node: Node<'node>,
        entries: Vec<KeywordArgumentInput<'node>>,
    },
}

pub(super) enum KeywordArgumentInput<'node> {
    Pair {
        key: Node<'node>,
        value: Node<'node>,
        name: Option<String>,
    },
    Splat(Option<Node<'node>>),
    Forwarded,
}

pub(super) struct KeywordArgument<'node> {
    pub(super) name: String,
    pub(super) node: Node<'node>,
    pub(super) type_: Type,
}

#[derive(Default)]
pub(super) struct CallArguments<'node> {
    pub(super) argument_nodes: Vec<Node<'node>>,
    pub(super) argument_types: Vec<Type>,
    pub(super) argument_indices: Vec<usize>,
    pub(super) positional_indices: Vec<usize>,
    pub(super) positional_types: Vec<Type>,
    pub(super) keyword_arguments: Vec<KeywordArgument<'node>>,
    pub(super) has_keyword_splat: bool,
    pub(super) has_dynamic_positional_splat: bool,
    pub(super) dynamic_positional_splat_types: Vec<Type>,
    pub(super) has_dynamic_keyword_splat: bool,
    pub(super) has_unknown_positional_splat: bool,
    pub(super) has_unknown_keyword_splat: bool,
    /// The call uses Ruby's `...` forwarding form. There is no concrete
    /// argument list at this syntax site; it is the caller's complete
    /// positional, keyword, and block argument set.
    pub(super) forwards_arguments: bool,
}

pub(super) struct CallArgumentEvaluation<'node> {
    pub(super) arguments: CallArguments<'node>,
    pub(super) abrupt: OutcomeTypes,
    pub(super) abrupt_flow: Flow,
    pub(super) all_normal: bool,
}

pub(super) struct IndexAccess<'node> {
    pub(super) receiver_type: Type,
    pub(super) arguments: CallArguments<'node>,
    pub(super) abrupt: OutcomeTypes,
    pub(super) abrupt_flow: Flow,
    pub(super) all_normal: bool,
}

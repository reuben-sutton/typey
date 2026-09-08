//! Owned shapes used at the boundary between Ruby call syntax and dispatch.
//!
//! The recursive evaluator keeps its parser-node call adapter separately. The
//! owned shapes here are the stable semantic vocabulary consumed by CFG
//! transfer.

use super::{
    optional_proc_type, proc_parts, Analyzer, Eval, Flow, MethodKey, OutcomeTypes, SourceSite,
};
use crate::cfg;
use crate::hir;
use crate::prism;
use crate::signature::MethodSig;
use crate::types::Type;
use ruby_prism::{ArgumentsNode, CallNode, Node};
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

#[derive(Clone, Debug)]
struct OwnedKeywordArgument {
    name: String,
    name_site: SourceSite,
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
                site: argument.name_site,
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

/// A call shape whose semantic fields come from owned HIR. During this
/// migration the Prism call is retained only as a child-node bridge so the
/// existing evaluator can still evaluate receiver and argument expressions.
/// The evaluator itself never asks the Prism node to decide the call shape.
pub(super) struct HirCallView<'node> {
    pub(super) call: hir::Call,
    pub(super) prism_call: CallNode<'node>,
}

impl<'node> HirCallView<'node> {
    pub(super) fn name(&self) -> String {
        self.call.name.as_str().to_owned()
    }

    pub(super) fn argument_inputs(&self) -> Vec<CallArgumentInput<'node>> {
        hir_call_argument_inputs(&self.call.arguments, self.prism_call.arguments())
    }

    pub(super) fn receiver(&self) -> Option<Node<'node>> {
        match self.call.receiver {
            hir::Receiver::Explicit(_) => self.prism_call.receiver(),
            hir::Receiver::Implicit | hir::Receiver::Super | hir::Receiver::Yield => None,
        }
    }

    pub(super) fn block(&self) -> Option<Node<'node>> {
        self.call.block.as_ref().and(self.prism_call.block())
    }

    pub(super) fn is_safe_navigation(&self) -> bool {
        self.call.safe_navigation
    }
}

pub(super) fn prism_call_argument_inputs<'node>(
    arguments: Option<ArgumentsNode<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    arguments.map_or_else(Vec::new, |arguments| {
        prism_argument_inputs_from_nodes(arguments.arguments().into_iter().collect())
    })
}

fn prism_argument_inputs_from_nodes<'node>(
    arguments: Vec<Node<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    arguments
        .into_iter()
        .map(|argument| {
            if argument.as_forwarding_arguments_node().is_some() {
                return CallArgumentInput::Forwarded { node: argument };
            }
            if let Some(splat) = argument.as_splat_node() {
                return CallArgumentInput::Splat {
                    node: argument,
                    expression: splat.expression(),
                };
            }
            if let Some(keyword_hash) = argument.as_keyword_hash_node() {
                let entries = keyword_hash
                    .elements()
                    .into_iter()
                    .map(|child| {
                        if let Some(assoc) = child.as_assoc_node() {
                            let key = assoc.key();
                            let name = key.as_symbol_node().map(|symbol| {
                                String::from_utf8_lossy(symbol.unescaped()).into_owned()
                            });
                            KeywordArgumentInput::Pair {
                                key,
                                value: assoc.value(),
                                name,
                            }
                        } else if let Some(splat) = child.as_assoc_splat_node() {
                            splat
                                .value()
                                .map_or(KeywordArgumentInput::Forwarded, |value| {
                                    KeywordArgumentInput::Splat(Some(value))
                                })
                        } else {
                            KeywordArgumentInput::Forwarded
                        }
                    })
                    .collect();
                return CallArgumentInput::KeywordHash {
                    node: argument,
                    entries,
                };
            }
            CallArgumentInput::Positional { node: argument }
        })
        .collect()
}

fn call_argument_input_kind<'node>(input: &CallArgumentInput<'node>) -> &'static str {
    match input {
        CallArgumentInput::Forwarded { .. } => "forwarded",
        CallArgumentInput::Positional { .. } => "positional",
        CallArgumentInput::Splat { .. } => "splat",
        CallArgumentInput::KeywordHash { .. } => "keyword hash",
    }
}

pub(super) fn hir_call_argument_inputs<'node>(
    arguments: &[hir::Argument],
    prism_arguments: Option<ArgumentsNode<'node>>,
) -> Vec<CallArgumentInput<'node>> {
    let mut raw = prism_call_argument_inputs(prism_arguments).into_iter();
    let mut result = Vec::with_capacity(arguments.len());
    let mut hir_index = 0;
    while hir_index < arguments.len() {
        match &arguments[hir_index] {
            hir::Argument::Keyword { .. } | hir::Argument::KeywordSplat(_) => {
                let (node, raw_entries) = match raw.next() {
                    Some(CallArgumentInput::KeywordHash { node, entries }) => (node, entries),
                    Some(_) | None => {
                        panic!("HIR keyword arguments did not match Prism argument bridge")
                    }
                };
                let mut raw_entries = raw_entries.into_iter();
                let mut hir_entries = Vec::new();
                while let Some(argument) = arguments.get(hir_index) {
                    match argument {
                        hir::Argument::Keyword { name, .. } => {
                            let Some(KeywordArgumentInput::Pair { key, value, .. }) =
                                raw_entries.next()
                            else {
                                panic!("HIR keyword argument has no Prism child bridge");
                            };
                            hir_entries.push(KeywordArgumentInput::Pair {
                                key,
                                value,
                                name: Some(name.as_str().to_owned()),
                            });
                            hir_index += 1;
                        }
                        hir::Argument::KeywordSplat(_) => {
                            let Some(KeywordArgumentInput::Splat(value)) = raw_entries.next()
                            else {
                                panic!("HIR keyword splat has no Prism child bridge");
                            };
                            hir_entries.push(KeywordArgumentInput::Splat(value));
                            hir_index += 1;
                        }
                        _ => break,
                    }
                }
                result.push(CallArgumentInput::KeywordHash {
                    node,
                    entries: hir_entries,
                });
            }
            hir::Argument::Positional(_) => match raw.next() {
                Some(CallArgumentInput::Positional { node }) => {
                    result.push(CallArgumentInput::Positional { node });
                    hir_index += 1;
                }
                Some(CallArgumentInput::KeywordHash { node, .. }) => {
                    // Prism uses the keyword-hash node for brace-less hash
                    // arguments too. The HIR lowerer has already decided
                    // whether that syntax is a keyword group or a positional
                    // hash; preserve the HIR decision here.
                    result.push(CallArgumentInput::Positional { node });
                    hir_index += 1;
                }
                Some(input) => panic!(
                    "HIR positional argument did not match Prism argument bridge: raw {} at {:?}, HIR {arguments:?}",
                    call_argument_input_kind(&input),
                    prism::span(match &input {
                        CallArgumentInput::Forwarded { node }
                        | CallArgumentInput::Positional { node }
                        | CallArgumentInput::Splat { node, .. }
                        | CallArgumentInput::KeywordHash { node, .. } => node,
                    }),
                ),
                None => panic!(
                    "HIR positional argument has no Prism child bridge: HIR {arguments:?}"
                ),
            },
            hir::Argument::Splat(_) => match raw.next() {
                Some(CallArgumentInput::Splat { node, expression }) => {
                    result.push(CallArgumentInput::Splat { node, expression });
                    hir_index += 1;
                }
                Some(_) | None => panic!("HIR splat did not match Prism argument bridge"),
            },
            hir::Argument::Forwarded => match raw.next() {
                Some(CallArgumentInput::Forwarded { node }) => {
                    result.push(CallArgumentInput::Forwarded { node });
                    hir_index += 1;
                }
                Some(_) | None => panic!("HIR forwarding did not match Prism argument bridge"),
            },
        }
    }
    assert!(
        raw.next().is_none(),
        "Prism argument bridge contains a shape not represented by HIR"
    );
    result
}

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_yield_result(
        &mut self,
        site: SourceSite,
        arguments: &CallArguments<'_>,
        environment: &mut super::Environment,
    ) -> Option<Type> {
        let key = environment.method_key.clone()?;
        let (expected, return_type) = {
            let state = self.declarations.methods.get(&key)?;
            let expected = state
                .block
                .as_ref()
                .and_then(proc_parts)
                .map(|(parameters, _)| parameters.to_vec());
            let return_type = state.block_return_type.clone().unwrap_or(Type::Any);
            (expected, return_type)
        };
        if let Some(expected) = expected.as_ref() {
            for (index, actual) in arguments.argument_types.iter().enumerate() {
                if let Some(expected) = expected.get(index) {
                    if !self.is_assignable(actual, expected) {
                        let argument_site =
                            arguments.argument_sites.get(index).copied().unwrap_or(site);
                        if let Some(argument) = arguments.argument_nodes.get(index) {
                            self.error(
                                argument,
                                format!(
                                    "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                                ),
                            );
                        } else {
                            self.error_at(
                                argument_site,
                                format!(
                                    "Expected `{expected}` but found `{actual}` for argument `arg{index}`"
                                ),
                            );
                        }
                    }
                }
            }
        }
        if let Some(state) = self.declarations.methods.get_mut(&key) {
            if state.observe_yield_arguments(&arguments.argument_types) {
                self.fixpoint.changed_methods.insert(key);
            }
        }
        Some(return_type)
    }

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
    ) -> Option<Eval> {
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(closure) => {
                if block_node.is_some() {
                    self.observe_block_call(
                        key,
                        block_node,
                        signature,
                        arguments,
                        Some(receiver_type),
                        environment,
                    )
                    .map(Eval::value)
                } else {
                    self.cfg_inline_block_return_type(
                        input,
                        *closure,
                        key,
                        signature,
                        arguments,
                        receiver_type,
                        environment,
                    )
                }
            }
            cfg::BlockOperand::Passed(value) => {
                let expected = signature.block.as_ref().and_then(optional_proc_type);
                if let (Some(expected), Some(name)) =
                    (expected.as_ref(), self.cfg_passed_symbol_name(input))
                {
                    return Some(Eval::value(self.eval_symbol_passed_block_named(
                        None,
                        input.site,
                        &name,
                        expected,
                        environment,
                    )));
                }
                if let (Some(block), Some(expected)) = (block_node, expected.as_ref()) {
                    if block
                        .as_block_argument_node()
                        .and_then(|block| block.expression())
                        .and_then(|expression| expression.as_symbol_node())
                        .is_some()
                    {
                        return Some(Eval::value(self.eval_symbol_passed_block(
                            block,
                            expected,
                            environment,
                        )));
                    }
                }
                values
                    .get(value.0 as usize)
                    .and_then(Option::as_ref)
                    .and_then(proc_parts)
                    .map(|(_, result)| Eval::value(result.clone()))
            }
        }
    }

    fn cfg_passed_symbol_name(&self, input: &OwnedCallInput) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.hir_program.expression(*block)?;
        match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name)) => Some(name.clone()),
            _ => None,
        }
    }

    pub(super) fn cfg_owned_hir_call_arguments(
        &mut self,
        input: &OwnedCallInput,
        call: &hir::Call,
        values: &[Option<Type>],
        fixed_array_elements: &HashMap<cfg::ValueId, Vec<cfg::ValueId>>,
        environment: &super::Environment,
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
                            value: _,
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
                            self.record_at(name_site, Type::Symbol, false, None);
                            call_arguments.keyword_arguments.push(OwnedKeywordArgument {
                                name: name.as_str().to_owned(),
                                name_site,
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
    pub(super) node: Option<Node<'node>>,
    pub(super) site: SourceSite,
    pub(super) type_: Type,
}

#[derive(Default)]
pub(super) struct CallArguments<'node> {
    pub(super) argument_nodes: Vec<Node<'node>>,
    pub(super) argument_sites: Vec<SourceSite>,
    pub(super) argument_types: Vec<Type>,
    pub(super) argument_indices: Vec<usize>,
    pub(super) positional_indices: Vec<usize>,
    pub(super) positional_types: Vec<Type>,
    pub(super) keyword_arguments: Vec<KeywordArgument<'node>>,
    pub(super) keyword_hash_indices: Vec<usize>,
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

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
    pub(super) defer_inline_assertion: bool,
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
            defer_inline_assertion: operation.defer_inline_assertion,
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
                        hir::Argument::Forwarded => {
                            let Some(KeywordArgumentInput::Forwarded) = raw_entries.next() else {
                                panic!("HIR keyword forwarding has no Prism child bridge");
                            };
                            hir_entries.push(KeywordArgumentInput::Forwarded);
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
                Some(CallArgumentInput::KeywordHash { node, entries })
                    if entries
                        .iter()
                        .all(|entry| matches!(entry, KeywordArgumentInput::Forwarded)) =>
                {
                    // A bare `**` is normalized by HIR to forwarded
                    // arguments, but Prism keeps it inside a keyword hash.
                    // Preserve the keyword-hash wrapper so argument
                    // evaluation retains its keyword-forwarding semantics.
                    result.push(CallArgumentInput::KeywordHash { node, entries });
                    hir_index += 1;
                }
                Some(CallArgumentInput::Splat {
                    node,
                    expression: None,
                }) => {
                    // Ruby's `*` forwarding syntax is represented by Prism as
                    // an empty splat, while HIR intentionally normalizes it
                    // to the same forwarded-arguments shape as `...`.
                    result.push(CallArgumentInput::Forwarded { node });
                    hir_index += 1;
                }
                Some(input) => panic!(
                    "HIR forwarding did not match Prism argument bridge: raw {} at {:?}, HIR {arguments:?}",
                    call_argument_input_kind(&input),
                    prism::span(match &input {
                        CallArgumentInput::Forwarded { node }
                        | CallArgumentInput::Positional { node }
                        | CallArgumentInput::Splat { node, .. }
                        | CallArgumentInput::KeywordHash { node, .. } => node,
                    }),
                ),
                None => panic!("HIR forwarding has no Prism child bridge: HIR {arguments:?}"),
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
        key: &MethodKey,
        signature: &MethodSig,
        arguments: &CallArguments<'node>,
        receiver_type: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<Eval> {
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(closure) => self.cfg_inline_block_return_type(
                input,
                *closure,
                key,
                signature,
                arguments,
                receiver_type,
                environment,
            ),
            cfg::BlockOperand::Passed(value) => {
                let mut bindings = self.infer_type_parameter_bindings(signature, arguments, None);
                bindings.extend(self.infer_generic_member_bindings(
                    signature,
                    arguments,
                    Some(receiver_type),
                ));
                let expected =
                    signature
                        .block
                        .as_ref()
                        .and_then(optional_proc_type)
                        .map(|expected| {
                            self.substitute_signature_type(
                                &expected,
                                Some(receiver_type),
                                &bindings,
                                &signature.type_parameters,
                            )
                        });
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
                values
                    .get(value.0 as usize)
                    .and_then(Option::as_ref)
                    .and_then(proc_parts)
                    .map(|(_, result)| Eval::value(result.clone()))
            }
        }
    }

    /// Evaluate a callback whose contract comes from a parser-free structural
    /// model rather than an RBI declaration. Collection methods are the main
    /// user of this path: their generic block contract is known even when the
    /// core RBI has no usable method signature.
    pub(super) fn cfg_owned_block_return_type(
        &mut self,
        input: &OwnedCallInput,
        expected_parameters: &[Type],
        expected_return: &Type,
        values: &[Option<Type>],
        environment: &mut super::Environment,
    ) -> Option<Eval> {
        let block_site = self.cfg_passed_block_site(input).unwrap_or(input.site);
        let expected = Type::Proc(
            expected_parameters.to_vec(),
            Box::new(expected_return.clone()),
        );
        match input.block.as_ref()? {
            cfg::BlockOperand::Inline(closure) => self.transfer_owned_closure_body(
                *closure,
                expected_parameters,
                Some(expected_return),
                None,
                environment,
            ),
            cfg::BlockOperand::Passed(value) => {
                let actual = values.get(value.0 as usize).cloned().flatten()?;
                if actual.is_nil() {
                    // `&nil` is Ruby's spelling for omitting a block.
                    return None;
                }
                if let Some(name) = self.cfg_passed_symbol_name(input) {
                    return Some(Eval::value(self.eval_symbol_passed_block_named(
                        None,
                        block_site,
                        &name,
                        &expected,
                        environment,
                    )));
                }
                let signature = Self::passed_block_signature(&actual)?;
                if !Self::passed_block_is_assignable(self, &signature, &expected) {
                    self.error_at(
                        block_site,
                        format!(
                            "Expected `{}` but found `{}` for block argument",
                            Self::block_type_description(&expected),
                            Self::block_type_description(&signature),
                        ),
                    );
                }
                let result = proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone());
                Some(Eval::value(result))
            }
        }
    }

    fn cfg_passed_block_site(&self, input: &OwnedCallInput) -> Option<SourceSite> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*block)?;
        let mut start = expression.span.start as usize;
        if start > 0 && self.program.source.get(start - 1) == Some(&b'&') {
            start -= 1;
        }
        Some(SourceSite::new(start, expression.span.end as usize))
    }

    fn cfg_passed_symbol_name(&self, input: &OwnedCallInput) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::BlockArgument::Passed(block) = call.block.as_ref()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*block)?;
        match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name)) => Some(name.clone()),
            _ => None,
        }
    }

    pub(super) fn cfg_dynamic_instance_variable_name(
        &self,
        input: &OwnedCallInput,
    ) -> Option<String> {
        let expression = input
            .expression
            .and_then(|expression| self.program.hir_program.expression(expression))?;
        let hir::ExprKind::Call(call) = &expression.kind else {
            return None;
        };
        let hir::Argument::Positional(argument) = call.arguments.first()? else {
            return None;
        };
        let expression = self.program.hir_program.expression(*argument)?;
        let name = match &expression.kind {
            hir::ExprKind::Literal(hir::Literal::Symbol(name)) => name.clone(),
            // HIR string literals retain their source spelling. Dynamic ivar
            // APIs conventionally receive symbols, but accept the ordinary
            // quoted-string form as well when it is statically known.
            hir::ExprKind::Literal(hir::Literal::String(name)) => name
                .strip_prefix('"')
                .and_then(|name| name.strip_suffix('"'))
                .or_else(|| {
                    name.strip_prefix('\'')
                        .and_then(|name| name.strip_suffix('\''))
                })
                .map(str::to_owned)?,
            _ => return None,
        };
        name.starts_with('@').then_some(name)
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

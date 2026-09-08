//! Owned shapes used at the boundary between Ruby call syntax and dispatch.
//!
//! The recursive evaluator still stores parser nodes on these shapes for
//! diagnostics and builtin hooks. Keeping the call vocabulary in its own
//! layer makes that dependency explicit and gives CFG transfer a stable place
//! to introduce source-owned call inputs.

use super::{Flow, OutcomeTypes, SourceSite};
use crate::cfg;
use crate::hir;
use crate::types::Type;
use ruby_prism::Node;

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

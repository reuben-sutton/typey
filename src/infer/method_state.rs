use super::{
    method_types::{merge_method_signatures, proc_parts},
    AccessorKind, Visibility,
};
use crate::hir;
use crate::prism;
use crate::signature::{self, MethodSig};
use crate::types::Type;
use ruby_prism::ParametersNode;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BlockReceiverBinding {
    Instance,
    Receiver,
    Both,
}

impl BlockReceiverBinding {
    pub(super) fn join(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        Self::Both
    }
}

/// The evolving summary for one user-defined method. A missing parameter or
/// return type means that no concrete evidence has reached that slot yet;
/// calls use `Never` provisionally so unresolved calls do not poison the
/// surrounding expression with `Any` before a later round can fill the slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct MethodState {
    pub(super) params: Vec<Option<Type>>,
    pub(super) rest_index: Option<usize>,
    pub(super) keywords: BTreeMap<String, Option<Type>>,
    pub(super) yield_params: Vec<Option<Type>>,
    pub(super) block_return_type: Option<Type>,
    pub(super) block_return_provisional: bool,
    pub(super) block: Option<Type>,
    pub(super) block_receiver_binding: Option<BlockReceiverBinding>,
    pub(super) required_keywords: BTreeSet<String>,
    pub(super) return_type: Option<Type>,
    pub(super) return_terminates: bool,
    /// The concrete exception type observed on an abrupt raise path. This is
    /// separate from `return_type`: a method may return normally on one path
    /// and raise on another, while a `T.noreturn` method still needs its
    /// exception type when called from a rescue clause.
    pub(super) raise_type: Option<Type>,
    pub(super) required_params: usize,
    pub(super) accepts_rest: bool,
    pub(super) accepts_keyword_rest: bool,
    pub(super) is_void: bool,
    pub(super) is_abstract: bool,
    pub(super) visibility: Visibility,
    pub(super) explicit: bool,
    pub(super) overloads: Vec<MethodSig>,
}

impl MethodState {
    pub(super) fn observe_block_receiver_binding(&mut self, binding: BlockReceiverBinding) -> bool {
        if self.explicit {
            return false;
        }
        let next = self
            .block_receiver_binding
            .map_or(binding, |current| current.join(binding));
        if self.block_receiver_binding == Some(next) {
            return false;
        }
        self.block_receiver_binding = Some(next);
        true
    }

    pub(super) fn explicit_overloads(signatures: &[MethodSig]) -> Self {
        let signature = merge_method_signatures(signatures);
        let (yield_params, block_return_type) = signature
            .block
            .as_ref()
            .and_then(|block| {
                proc_parts(block).map(|(parameters, return_type)| {
                    (
                        parameters.iter().cloned().map(Some).collect(),
                        Some(return_type.clone()),
                    )
                })
            })
            .unwrap_or_default();
        Self {
            params: signature.params.iter().cloned().map(Some).collect(),
            rest_index: signature.rest_index,
            keywords: signature
                .keywords
                .iter()
                .map(|(name, parameter)| (name.clone(), Some(parameter.type_.clone())))
                .collect(),
            yield_params,
            block_return_type,
            block_return_provisional: false,
            block: signature.block.clone(),
            block_receiver_binding: None,
            required_keywords: signature
                .keywords
                .iter()
                .filter_map(|(name, parameter)| parameter.required.then_some(name.clone()))
                .collect(),
            return_type: Some(signature.return_type.clone()),
            return_terminates: signature.return_type.is_never(),
            raise_type: None,
            required_params: signature.required_params,
            accepts_rest: signature.accepts_rest,
            accepts_keyword_rest: signature.accepts_keyword_rest,
            is_void: signature.is_void,
            is_abstract: signature.is_abstract,
            visibility: Visibility::Public,
            explicit: true,
            overloads: signatures.to_vec(),
        }
    }

    pub(super) fn inferred<'node>(parameters: Option<ParametersNode<'node>>) -> Self {
        let mut params = Vec::new();
        let mut keywords = BTreeMap::new();
        let mut required_keywords = BTreeSet::new();
        let mut required_params = 0;
        let mut rest_index = None;

        if let Some(parameters) = parameters {
            for _ in &parameters.requireds() {
                params.push(None);
                required_params += 1;
            }
            for _ in &parameters.optionals() {
                params.push(None);
            }
            let accepts_rest = parameters.rest().is_some()
                || parameters
                    .keyword_rest()
                    .is_some_and(|node| node.as_forwarding_parameter_node().is_some());
            if accepts_rest {
                rest_index = Some(params.len());
                params.push(None);
            }
            for _ in &parameters.posts() {
                params.push(None);
                required_params += 1;
            }
            for parameter in &parameters.keywords() {
                if let Some(required) = parameter.as_required_keyword_parameter_node() {
                    let name = prism::constant_name(required.name());
                    keywords.insert(name.clone(), None);
                    required_keywords.insert(name);
                } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                    keywords.insert(prism::constant_name(optional.name()), None);
                }
            }
            return Self {
                params,
                rest_index,
                keywords,
                yield_params: Vec::new(),
                block_return_type: None,
                block_return_provisional: false,
                block: None,
                block_receiver_binding: None,
                required_keywords,
                return_type: None,
                return_terminates: false,
                raise_type: None,
                required_params,
                accepts_rest,
                accepts_keyword_rest: parameters.keyword_rest().is_some_and(|node| {
                    node.as_keyword_rest_parameter_node().is_some()
                        || node.as_forwarding_parameter_node().is_some()
                }),
                is_void: false,
                is_abstract: false,
                visibility: Visibility::Public,
                explicit: false,
                overloads: Vec::new(),
            };
        }

        Self {
            params,
            rest_index,
            keywords,
            yield_params: Vec::new(),
            block_return_type: None,
            block_return_provisional: false,
            block: None,
            block_receiver_binding: None,
            required_keywords,
            return_type: None,
            return_terminates: false,
            raise_type: None,
            required_params,
            accepts_rest: false,
            accepts_keyword_rest: false,
            is_void: false,
            is_abstract: false,
            visibility: Visibility::Public,
            explicit: false,
            overloads: Vec::new(),
        }
    }

    pub(super) fn inferred_hir(parameters: &hir::Parameters) -> Self {
        let mut state = Self::inferred(None);
        let mut positional_index = 0;
        for parameter in &parameters.parameters {
            match parameter.kind {
                hir::ParameterKind::Required => {
                    state.params.push(None);
                    state.required_params += 1;
                    positional_index += 1;
                }
                hir::ParameterKind::Optional => {
                    state.params.push(None);
                    positional_index += 1;
                }
                hir::ParameterKind::Rest => {
                    state.rest_index = Some(positional_index);
                    state.params.push(None);
                    state.accepts_rest = true;
                    positional_index += 1;
                }
                hir::ParameterKind::Forwarded => {
                    if state.accepts_rest {
                        state.accepts_keyword_rest = true;
                    } else {
                        state.rest_index = Some(positional_index);
                        state.params.push(None);
                        state.accepts_rest = true;
                        positional_index += 1;
                    }
                }
                hir::ParameterKind::Post => {
                    state.params.push(None);
                    state.required_params += 1;
                    positional_index += 1;
                }
                hir::ParameterKind::RequiredKeyword => {
                    if let Some(name) = &parameter.name {
                        state.required_keywords.insert(name.as_str().to_owned());
                        state.keywords.insert(name.as_str().to_owned(), None);
                    }
                }
                hir::ParameterKind::OptionalKeyword => {
                    if let Some(name) = &parameter.name {
                        state.keywords.insert(name.as_str().to_owned(), None);
                    }
                }
                hir::ParameterKind::KeywordRest => {
                    state.accepts_keyword_rest = true;
                }
                hir::ParameterKind::Block | hir::ParameterKind::Anonymous => {}
            }
        }
        state
    }

    pub(super) fn inferred_accessor(kind: AccessorKind) -> Self {
        let mut state = Self::inferred(None);
        state.return_type = Some(Type::Any);
        state.block_receiver_binding = None;
        if kind == AccessorKind::Writer {
            state.params = vec![Some(Type::Any)];
            state.required_params = 1;
        }
        state
    }

    pub(super) fn body_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            parameter_kinds: Vec::new(),
            param_names: Vec::new(),
            return_type: Type::Any,
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
            rest_index: self.rest_index,
            keywords: self
                .keywords
                .iter()
                .map(|(name, type_)| {
                    (
                        name.clone(),
                        signature::KeywordParam {
                            type_: type_.clone().unwrap_or(Type::Any),
                            required: self.required_keywords.contains(name),
                        },
                    )
                })
                .collect(),
            accepts_keyword_rest: self.accepts_keyword_rest,
            type_parameters: Vec::new(),
            block: self.block.clone(),
            is_void: false,
            is_abstract: self.is_abstract,
        }
    }

    pub(super) fn call_signature(&self) -> MethodSig {
        MethodSig {
            params: self
                .params
                .iter()
                .map(|type_| type_.clone().unwrap_or(Type::Any))
                .collect(),
            parameter_kinds: Vec::new(),
            param_names: Vec::new(),
            return_type: self.return_type.clone().unwrap_or(Type::Never),
            required_params: self.required_params,
            accepts_rest: self.accepts_rest,
            rest_index: self.rest_index,
            keywords: self
                .keywords
                .iter()
                .map(|(name, type_)| {
                    (
                        name.clone(),
                        signature::KeywordParam {
                            type_: type_.clone().unwrap_or(Type::Any),
                            required: self.required_keywords.contains(name),
                        },
                    )
                })
                .collect(),
            accepts_keyword_rest: self.accepts_keyword_rest,
            type_parameters: Vec::new(),
            block: self.block.clone().or_else(|| {
                (!self.yield_params.is_empty() || self.block_return_type.is_some()).then(|| {
                    Type::Proc(
                        self.block_parameters(),
                        Box::new(self.block_return_type.clone().unwrap_or(Type::Any)),
                    )
                })
            }),
            is_void: self.is_void,
            is_abstract: self.is_abstract,
        }
    }

    pub(super) fn observe_argument(&mut self, index: usize, actual: &Type) -> bool {
        if self.explicit {
            return false;
        }
        let Some(slot) = self.params.get_mut(index) else {
            return false;
        };
        let next = slot
            .as_ref()
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if slot.as_ref() == Some(&next) {
            false
        } else {
            *slot = Some(next);
            true
        }
    }

    pub(super) fn observe_arguments(&mut self, actuals: &[Type]) -> bool {
        if self.explicit {
            return false;
        }
        let Some(rest_index) = self.rest_index else {
            return actuals
                .iter()
                .enumerate()
                .fold(false, |changed, (index, actual)| {
                    self.observe_argument(index, actual) || changed
                });
        };

        let post_count = self.params.len().saturating_sub(rest_index + 1);
        let has_all_posts = actuals.len() >= rest_index + post_count;
        let post_start = if has_all_posts {
            actuals.len().saturating_sub(post_count)
        } else {
            actuals.len()
        };
        let mut changed = false;
        for (index, actual) in actuals.iter().enumerate() {
            let slot_index = if index < rest_index {
                index
            } else if has_all_posts && index >= post_start {
                rest_index + 1 + index - post_start
            } else {
                rest_index
            };
            changed |= self.observe_argument(slot_index, actual);
        }
        changed
    }

    pub(super) fn observe_keyword(&mut self, name: &str, actual: &Type) -> bool {
        if self.explicit {
            return false;
        }
        let Some(slot) = self.keywords.get_mut(name) else {
            return false;
        };
        let next = slot
            .as_ref()
            .map_or_else(|| actual.clone(), |current| current.join(actual));
        if slot.as_ref() == Some(&next) {
            false
        } else {
            *slot = Some(next);
            true
        }
    }

    pub(super) fn block_parameters(&self) -> Vec<Type> {
        if let Some(block) = &self.block {
            if let Some((parameters, _)) = proc_parts(block) {
                return parameters.to_vec();
            }
        }
        self.yield_params
            .iter()
            .map(|type_| type_.clone().unwrap_or(Type::Any))
            .collect()
    }

    pub(super) fn block_result_type(&self) -> Type {
        self.block
            .as_ref()
            .and_then(|block| proc_parts(block).map(|(_, result)| result.clone()))
            .or_else(|| self.block_return_type.clone())
            .unwrap_or(Type::Any)
    }

    pub(super) fn observe_yield_arguments(&mut self, actual: &[Type]) -> bool {
        let mut changed = false;
        for (index, actual) in actual.iter().enumerate() {
            if index >= self.yield_params.len() {
                self.yield_params.push(Some(actual.clone()));
                changed = true;
                continue;
            }
            let slot = &mut self.yield_params[index];
            let next = slot
                .as_ref()
                .map_or_else(|| actual.clone(), |current| current.join(actual));
            if slot.as_ref() != Some(&next) {
                *slot = Some(next);
                changed = true;
            }
        }
        changed
    }

    pub(super) fn observe_block_return(&mut self, actual: &Type) -> bool {
        self.observe_block_return_with_provenance(actual, false)
    }

    pub(super) fn observe_provisional_block_return(&mut self, actual: &Type) -> bool {
        self.observe_block_return_with_provenance(actual, true)
    }

    pub(super) fn observe_forwarded_block_return(&mut self, actual: &Type) -> bool {
        if self.block_return_type.as_ref().is_some_and(
            |type_| matches!(type_, Type::TypeVar(name) if name.starts_with("$block_return:")),
        ) && !actual.contains_any()
        {
            let changed =
                self.block_return_type.as_ref() != Some(actual) || self.block_return_provisional;
            self.block_return_type = Some(actual.clone());
            self.block_return_provisional = false;
            changed
        } else {
            self.observe_block_return(actual)
        }
    }

    fn observe_block_return_with_provenance(&mut self, actual: &Type, provisional: bool) -> bool {
        let (next, next_provisional) = match &self.block_return_type {
            None => (actual.clone(), provisional),
            Some(_) if self.block_return_provisional && !actual.contains_any() => {
                (actual.clone(), false)
            }
            Some(current) => (
                current.join(actual),
                self.block_return_provisional && provisional,
            ),
        };
        let changed = self.block_return_type.as_ref() != Some(&next)
            || self.block_return_provisional != next_provisional;
        self.block_return_type = Some(next);
        self.block_return_provisional = next_provisional;
        changed
    }
}

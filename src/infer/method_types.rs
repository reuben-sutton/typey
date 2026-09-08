use super::prism;
use crate::signature::{self, MethodSig};
use crate::types::Type;
use ruby_prism::{Node, ParametersNode};
use std::collections::BTreeMap;

/// The parser-facing parameter shape used to adapt a declared signature to
/// Ruby's actual positional, keyword, rest, and block parameters.
#[derive(Clone, Debug, Default)]
pub(super) struct ParameterShape {
    pub(super) parameter_kinds: Vec<(String, signature::ParameterKind)>,
    pub(super) required_positional: usize,
    pub(super) accepts_rest: bool,
    pub(super) rest_index: Option<usize>,
    pub(super) keywords: BTreeMap<String, bool>,
    pub(super) accepts_keyword_rest: bool,
    pub(super) has_block: bool,
    pub(super) block_name: Option<String>,
}

impl ParameterShape {
    pub(super) fn from_parameters<'node>(
        source: &[u8],
        parameters: Option<ParametersNode<'node>>,
    ) -> Self {
        let Some(parameters) = parameters else {
            return Self::default();
        };
        let required_positional = parameters.requireds().len();
        let accepts_rest = parameters.rest().is_some()
            || parameters
                .keyword_rest()
                .is_some_and(|node| node.as_forwarding_parameter_node().is_some());
        let rest_index = parameters
            .rest()
            .map(|_| parameters.requireds().len() + parameters.optionals().len());
        let mut keywords = BTreeMap::new();
        let mut parameter_kinds = Vec::new();
        let parameter_name = |parameter: &Node<'_>| {
            parameter
                .as_required_parameter_node()
                .map(|parameter| prism::constant_name(parameter.name()))
                .or_else(|| {
                    parameter
                        .as_optional_parameter_node()
                        .map(|parameter| prism::constant_name(parameter.name()))
                })
                .unwrap_or_else(|| prism::text(source, parameter))
        };
        for parameter in &parameters.requireds() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::Positional,
            ));
        }
        for parameter in &parameters.optionals() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::OptionalPositional,
            ));
        }
        if let Some(rest) = parameters
            .rest()
            .and_then(|node| node.as_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                parameter_kinds.push((
                    prism::constant_name(name),
                    signature::ParameterKind::RestPositional,
                ));
            }
        }
        for parameter in &parameters.posts() {
            parameter_kinds.push((
                parameter_name(&parameter),
                signature::ParameterKind::Positional,
            ));
        }
        for parameter in &parameters.keywords() {
            if let Some(required) = parameter.as_required_keyword_parameter_node() {
                keywords.insert(prism::constant_name(required.name()), true);
                parameter_kinds.push((
                    prism::constant_name(required.name()),
                    signature::ParameterKind::Keyword,
                ));
            } else if let Some(optional) = parameter.as_optional_keyword_parameter_node() {
                keywords.insert(prism::constant_name(optional.name()), false);
                parameter_kinds.push((
                    prism::constant_name(optional.name()),
                    signature::ParameterKind::OptionalKeyword,
                ));
            }
        }
        if let Some(rest) = parameters
            .keyword_rest()
            .and_then(|node| node.as_keyword_rest_parameter_node())
        {
            if let Some(name) = rest.name() {
                parameter_kinds.push((
                    prism::constant_name(name),
                    signature::ParameterKind::RestKeyword,
                ));
            }
        }
        if let Some(block) = parameters.block() {
            if let Some(name) = block.name() {
                parameter_kinds.push((prism::constant_name(name), signature::ParameterKind::Block));
            }
        }
        Self {
            parameter_kinds,
            required_positional,
            accepts_rest,
            rest_index,
            keywords,
            accepts_keyword_rest: parameters.keyword_rest().is_some_and(|node| {
                node.as_keyword_rest_parameter_node().is_some()
                    || node.as_forwarding_parameter_node().is_some()
            }),
            has_block: parameters.block().is_some(),
            block_name: parameters
                .block()
                .and_then(|block| block.name())
                .map(prism::constant_name),
        }
    }
}

pub(super) fn apply_parameter_shape(signature: &MethodSig, shape: &ParameterShape) -> MethodSig {
    if signature.param_names.is_empty() || signature.param_names.len() != signature.params.len() {
        return signature.clone();
    }

    let mut result = signature.clone();
    let mut params = Vec::new();
    let mut keywords = result.keywords.clone();
    let mut block = result.block.clone();
    for (name, type_) in signature.param_names.iter().zip(&signature.params) {
        let is_block_parameter =
            shape.has_block && (name == "&" || shape.block_name.as_deref() == Some(name.as_str()));
        if is_block_parameter && optional_proc_type(type_).is_some() {
            // Preserve nilability for optional `&blk` parameters.
            block = Some(type_.clone());
            continue;
        }
        if let Some(required) = shape.keywords.get(name) {
            keywords.insert(
                name.clone(),
                signature::KeywordParam {
                    type_: type_.clone(),
                    required: *required,
                },
            );
            continue;
        }
        params.push(type_.clone());
    }
    result.params = params;
    result.param_names.clear();
    result.required_params = shape.required_positional.min(result.params.len());
    result.accepts_rest |= shape.accepts_rest;
    result.rest_index = shape.rest_index;
    result.accepts_keyword_rest |= shape.accepts_keyword_rest;
    result.keywords = keywords;
    result.block = block;
    result
}

pub(super) fn optional_proc_type(type_: &Type) -> Option<Type> {
    match type_ {
        Type::Proc(_, _) | Type::BoundProc { .. } => Some(type_.clone()),
        Type::Union(members)
            if members.iter().all(|member| {
                member.is_nil() || matches!(member, Type::Proc(_, _) | Type::BoundProc { .. })
            }) =>
        {
            members.iter().find_map(|member| {
                matches!(member, Type::Proc(_, _) | Type::BoundProc { .. }).then(|| member.clone())
            })
        }
        _ => None,
    }
}

pub(super) fn proc_parts(type_: &Type) -> Option<(&[Type], &Type)> {
    match type_ {
        Type::Proc(parameters, result) => Some((parameters, result)),
        Type::BoundProc {
            parameters, result, ..
        } => Some((parameters, result)),
        _ => None,
    }
}

pub(super) fn proc_arity_narrowing(type_: &Type, arity: usize) -> Option<Type> {
    match type_ {
        Type::Proc(_, result) => Some(Type::Proc(vec![Type::Any; arity], result.clone())),
        Type::BoundProc {
            receiver, result, ..
        } => Some(Type::BoundProc {
            receiver: receiver.clone(),
            parameters: vec![Type::Any; arity],
            result: result.clone(),
        }),
        Type::Union(members) => {
            let narrowed = members
                .iter()
                .filter_map(|member| proc_arity_narrowing(member, arity))
                .collect::<Vec<_>>();
            (!narrowed.is_empty()).then(|| Type::union(narrowed))
        }
        _ => None,
    }
}

pub(super) fn proc_receiver(type_: &Type) -> Option<&Type> {
    match type_ {
        Type::BoundProc { receiver, .. } => Some(receiver),
        _ => None,
    }
}

pub(super) fn merge_method_signatures(signatures: &[MethodSig]) -> MethodSig {
    let Some(first) = signatures.first() else {
        return MethodSig::new(Vec::new(), Type::Any);
    };
    let parameter_count = signatures
        .iter()
        .map(|signature| signature.params.len())
        .max()
        .unwrap_or(0);
    let params = (0..parameter_count)
        .map(|index| {
            signatures.iter().fold(Type::Never, |current, signature| {
                current.join(signature.params.get(index).unwrap_or(&Type::Any))
            })
        })
        .collect();
    let mut keywords = BTreeMap::new();
    for signature in signatures {
        for (name, parameter) in &signature.keywords {
            let entry = keywords
                .entry(name.clone())
                .or_insert_with(|| signature::KeywordParam {
                    type_: Type::Never,
                    required: true,
                });
            entry.type_ = entry.type_.join(&parameter.type_);
            entry.required &= parameter.required;
        }
    }
    let return_type = signatures.iter().fold(Type::Never, |current, signature| {
        current.join(&signature.return_type)
    });
    MethodSig {
        params,
        parameter_kinds: Vec::new(),
        param_names: Vec::new(),
        return_type,
        required_params: signatures
            .iter()
            .map(|signature| signature.required_params)
            .min()
            .unwrap_or(first.required_params),
        accepts_rest: signatures.iter().any(|signature| signature.accepts_rest),
        rest_index: signatures
            .iter()
            .find(|signature| signature.accepts_rest)
            .and_then(|signature| signature.rest_index),
        keywords,
        accepts_keyword_rest: signatures
            .iter()
            .any(|signature| signature.accepts_keyword_rest),
        type_parameters: signatures
            .iter()
            .flat_map(|signature| signature.type_parameters.iter().cloned())
            .fold(Vec::new(), |mut names, name| {
                if !names.contains(&name) {
                    names.push(name);
                }
                names
            }),
        block: signatures
            .iter()
            .filter_map(|signature| signature.block.as_ref())
            .cloned()
            .reduce(|current, block| current.join(&block)),
        is_void: signatures.iter().all(|signature| signature.is_void),
        is_abstract: signatures.iter().all(|signature| signature.is_abstract),
    }
}

use super::{prism, proc_parts, Analyzer, CallSite, Environment};
use crate::types::Type;
use ruby_prism::Node;

impl<'src> Analyzer<'src> {
    pub(super) fn eval_array_method<'a, 'node>(
        &mut self,
        element: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "new" => Type::Array(Box::new(element.clone())),
            "map" | "collect" | "map!" | "collect!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_collection_block(block, element, environment)
                });
                Type::Array(Box::new(block_type))
            }
            "reduce" | "inject" => {
                let Some(block) = site.block else {
                    return Type::named("Enumerator");
                };
                let accumulator = site
                    .argument_types
                    .first()
                    .cloned()
                    .unwrap_or_else(|| element.clone());
                if let Some(symbol) = block
                    .as_block_argument_node()
                    .and_then(|block| block.expression())
                    .and_then(|expression| expression.as_symbol_node())
                {
                    let name = String::from_utf8_lossy(symbol.unescaped()).into_owned();
                    let argument_types = vec![element.clone()];
                    let argument_nodes = Vec::new();
                    let site = CallSite {
                        argument_nodes: &argument_nodes,
                        argument_types: &argument_types,
                        block: None,
                    };
                    self.eval_method_call(&accumulator, &name, &site, environment)
                } else if let Some(expression_type) =
                    self.passed_block_expression_type(block, environment)
                {
                    if let Some(signature) = Self::passed_block_signature(&expression_type) {
                        let expected = Type::Proc(
                            vec![accumulator.clone(), element.clone()],
                            Box::new(Type::Anything),
                        );
                        if !self.is_assignable(&signature, &expected) {
                            self.error(
                                block,
                                format!(
                                    "Expected `{}` but found `{}` for block argument",
                                    Self::block_type_description(&expected),
                                    Self::block_type_description(&signature),
                                ),
                            );
                        }
                        proc_parts(&signature).map_or(Type::Any, |(_, result)| result.clone())
                    } else {
                        Type::Any
                    }
                } else {
                    self.eval_block_node(block, &[accumulator, element.clone()], environment)
                }
            }
            "flat_map" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_collection_block(block, element, environment)
                });
                Type::Array(Box::new(self.flat_map_element_type(&block_type)))
            }
            "grep" => {
                let filtered = site
                    .argument_types
                    .first()
                    .and_then(Self::class_object_value_type)
                    .map(|expected| self.meet_predicate_type(element, &expected))
                    .unwrap_or_else(|| element.clone());
                Type::Array(Box::new(filtered))
            }
            "to_h" => {
                let pair_type = site.block.map_or_else(
                    || element.clone(),
                    |block| self.eval_collection_block(block, element, environment),
                );
                let (key, value) = Self::pair_types(&pair_type).unwrap_or((Type::Any, Type::Any));
                Type::Hash(Box::new(key), Box::new(value))
            }
            "each_with_object" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let object = site.argument_types.first().cloned().unwrap_or(Type::Any);
                if let Some(block) = site.block {
                    let expected = vec![element.clone(), object.clone()];
                    let accumulator_name = Self::block_parameter_name(block, 1);
                    let (_, block_environment) =
                        self.eval_block_node_with_environment(block, &expected, environment);
                    if let Some(name) = accumulator_name {
                        let refined = block_environment.get(&name);
                        if !refined.is_any() {
                            return refined;
                        }
                    }
                }
                object
            }
            "each_with_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let expected = vec![element.clone(), Type::Integer];
                    let _ = self.eval_block_node(block, &expected, environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "filter_map" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_collection_block(block, element, environment)
                });
                Type::Array(Box::new(block_type.truthy_part()))
            }
            "flatten" => Type::Array(Box::new(self.flattened_array_element_type(element))),
            "each" | "select" | "filter" | "reject" | "delete_if" | "sort" | "reverse"
            | "rotate" | "shuffle" => {
                if site.block.is_none()
                    && matches!(name, "each" | "select" | "filter" | "reject" | "delete_if")
                {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "reverse_each" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "uniq" => Type::Array(Box::new(element.clone())),
            "each_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::Integer], environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "find" | "detect" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "find_index" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Integer])
            }
            "index" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Integer])
            }
            "group_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let key = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(element), environment)
                });
                Type::Hash(
                    Box::new(key),
                    Box::new(Type::Array(Box::new(element.clone()))),
                )
            }
            "partition" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(Type::Array(Box::new(element.clone()))))
            }
            "take_while" | "drop_while" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "sort_by" | "sort_by!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "first" | "last" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "shift" | "pop" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "at" => Type::union([Type::Nil, element.clone()]),
            "fetch" => {
                if let Some(default) = site.argument_types.get(1) {
                    element.join(default)
                } else if let Some(block) = site.block {
                    let block_type = self.eval_block_node(block, &[Type::Integer], environment);
                    element.join(&block_type)
                } else {
                    element.clone()
                }
            }
            "[]" => {
                if site
                    .argument_types
                    .first()
                    .is_some_and(|type_| matches!(type_, Type::Integer))
                {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::union([Type::Nil, Type::Array(Box::new(element.clone()))])
                }
            }
            "[]=" => site.argument_types.last().cloned().unwrap_or(Type::Any),
            "values_at" => Type::Array(Box::new(element.clone())),
            "sample" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "min" | "max" => {
                if site.argument_types.is_empty() {
                    Type::union([Type::Nil, element.clone()])
                } else {
                    Type::Array(Box::new(element.clone()))
                }
            }
            "min_by" | "max_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "combination" | "repeated_combination" | "permutation" | "repeated_permutation" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let expected = Type::Array(Box::new(element.clone()));
                    let _ = self.eval_block_node(block, &[expected], environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "product" => {
                let mut tuple = vec![element.clone()];
                tuple.extend(
                    site.argument_types
                        .iter()
                        .map(|argument| self.array_element_type(argument)),
                );
                if let Some(block) = site.block {
                    let expected = Type::Array(Box::new(Type::Tuple(tuple.clone())));
                    let _ = self.eval_block_node(block, &[expected], environment);
                    Type::Array(Box::new(element.clone()))
                } else {
                    Type::Array(Box::new(Type::Tuple(tuple)))
                }
            }
            "pack" => Type::String,
            "compact" => Type::Array(Box::new(element.without(&Type::Nil))),
            "compact!" | "uniq!" => {
                Type::union([Type::Nil, Type::Array(Box::new(element.clone()))])
            }
            "length" | "size" => Type::Integer,
            "inspect" | "to_s" => Type::String,
            "count" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Integer
            }
            "empty?" | "include?" | "intersect?" => Type::bool(),
            "<=>" => {
                if site
                    .argument_types
                    .first()
                    .is_some_and(|other| self.definitely_comparable_array_element(element, other))
                {
                    Type::Integer
                } else {
                    Type::union([Type::Nil, Type::Integer])
                }
            }
            "any?" | "all?" | "none?" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::bool()
            }
            "join" => Type::String,
            "concat" => {
                let element = site
                    .argument_types
                    .iter()
                    .fold(element.clone(), |current, actual| {
                        current.join(&self.array_element_type(actual))
                    });
                Type::Array(Box::new(element))
            }
            "zip" => {
                let mut tuple = vec![element.clone()];
                tuple.extend(
                    site.argument_types
                        .iter()
                        .map(|argument| self.array_element_type(argument)),
                );
                Type::Array(Box::new(Type::Tuple(tuple)))
            }
            "sum" => {
                let element = site.block.map_or_else(
                    || element.clone(),
                    |block| self.eval_block_node(block, std::slice::from_ref(element), environment),
                );
                Self::numeric_sum_type(&element, site.argument_types.first())
            }
            "+" | "|" => {
                let element = site
                    .argument_types
                    .iter()
                    .fold(element.clone(), |current, actual| {
                        current.join(&self.array_element_type(actual))
                    });
                Type::Array(Box::new(element))
            }
            "-" | "&" => Type::Array(Box::new(element.clone())),
            "*" => match site.argument_types.first() {
                Some(Type::Integer) => Type::Array(Box::new(element.clone())),
                Some(Type::String) => Type::String,
                _ => Type::Any,
            },
            "take" | "drop" => Type::Array(Box::new(element.clone())),
            "fill" | "replace" | "clear" | "unshift" | "prepend" | "insert" | "reverse!"
            | "rotate!" | "shuffle!" | "sort!" => Type::Array(Box::new(element.clone())),
            "select!" | "filter!" | "reject!" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, Type::Array(Box::new(element.clone()))])
            }
            "keep_if" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::Array(Box::new(element.clone()))
            }
            "bsearch" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, std::slice::from_ref(element), environment);
                }
                Type::union([Type::Nil, element.clone()])
            }
            "push" | "<<" => {
                let mut result_element = element.clone();
                for (argument, actual) in site.argument_nodes.iter().zip(site.argument_types) {
                    let actual = self.tuple_literal_argument_type(argument, actual, element);
                    self.check_assignable(argument, &actual, element);
                    if !self.is_assignable(&actual, element) {
                        continue;
                    }
                    if result_element.is_any() && !actual.is_any() {
                        result_element = actual;
                    } else {
                        result_element = result_element.join(&actual);
                    }
                }
                Type::Array(Box::new(result_element))
            }
            "to_a" | "to_ary" => Type::Array(Box::new(element.clone())),
            "to_set" => {
                let element = site.block.map_or_else(
                    || element.clone(),
                    |block| self.eval_block_node(block, std::slice::from_ref(element), environment),
                );
                Type::Named("Set".to_owned(), vec![element])
            }
            _ => Type::Any,
        }
    }

    pub(super) fn definitely_comparable_array_element(&self, left: &Type, right: &Type) -> bool {
        match (left, right) {
            (Type::Integer, Type::Integer)
            | (Type::Integer, Type::Float)
            | (Type::Float, Type::Integer)
            | (Type::Float, Type::Float)
            | (Type::String, Type::String)
            | (Type::Symbol, Type::Symbol) => true,
            (left, Type::Array(right)) => self.definitely_comparable_array_element(left, right),
            (left, Type::Tuple(right)) => right
                .iter()
                .all(|right| self.definitely_comparable_array_element(left, right)),
            (Type::Union(left), right) => left
                .iter()
                .all(|left| self.definitely_comparable_array_element(left, right)),
            (left, Type::Union(right)) => right
                .iter()
                .all(|right| self.definitely_comparable_array_element(left, right)),
            _ => false,
        }
    }

    pub(super) fn definitely_comparable_array_tuple(&self, left: &[Type], right: &Type) -> bool {
        match right {
            Type::Tuple(right) if left.len() == right.len() => left
                .iter()
                .zip(right)
                .all(|(left, right)| self.definitely_comparable_array_element(left, right)),
            Type::Array(right) => left
                .iter()
                .all(|left| self.definitely_comparable_array_element(left, right)),
            _ => false,
        }
    }

    pub(super) fn tuple_literal_argument_type<'node>(
        &self,
        node: &Node<'node>,
        actual: &Type,
        expected: &Type,
    ) -> Type {
        let Type::Tuple(expected_elements) = expected else {
            return actual.clone();
        };
        let Some(array) = node.as_array_node() else {
            return actual.clone();
        };
        let elements = array.elements();
        if elements.len() != expected_elements.len()
            || elements
                .iter()
                .any(|element| element.as_splat_node().is_some())
        {
            return actual.clone();
        }

        let mut inferred = Vec::with_capacity(elements.len());
        for element in &elements {
            let span = prism::span(&element);
            let type_ = self
                .types
                .iter()
                .rev()
                .find(|inferred| {
                    inferred.start == span.0
                        && inferred.end == span.1
                        && !inferred.type_.contains_any()
                })
                .or_else(|| {
                    self.types
                        .iter()
                        .rev()
                        .find(|inferred| inferred.start == span.0 && inferred.end == span.1)
                })
                .map(|inferred| inferred.type_.clone());
            let Some(type_) = type_ else {
                return actual.clone();
            };
            inferred.push(type_);
        }
        Type::Tuple(inferred)
    }

    pub(super) fn eval_hash_method<'a, 'node>(
        &mut self,
        key: &Type,
        value: &Type,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "new" => Type::Hash(Box::new(key.clone()), Box::new(value.clone())),
            "[]" | "default" => Type::union([Type::Nil, value.clone()]),
            "dig" => Type::union([Type::Nil, value.clone()]),
            "[]=" => site.argument_types.last().cloned().unwrap_or(Type::Any),
            "fetch" => {
                if let Some(default) = site.argument_types.get(1) {
                    let empty_default = site.argument_nodes.get(1).is_some_and(|node| {
                        node.as_array_node()
                            .is_some_and(|array| array.elements().is_empty())
                            || node
                                .as_hash_node()
                                .is_some_and(|hash| hash.elements().is_empty())
                    });
                    if empty_default {
                        value.clone()
                    } else {
                        value.join(default)
                    }
                } else if let Some(block) = site.block {
                    let block_type =
                        self.eval_block_node(block, std::slice::from_ref(key), environment);
                    value.join(&block_type)
                } else {
                    value.clone()
                }
            }
            "fetch_values" => Type::Array(Box::new(value.clone())),
            "map" | "collect" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, &[key.clone(), value.clone()], environment)
                });
                Type::Array(Box::new(block_type))
            }
            "keys" => Type::Array(Box::new(key.clone())),
            "values" => Type::Array(Box::new(value.clone())),
            "each" | "each_pair" | "each_key" | "each_value" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let params = if name == "each_key" || name == "each_value" {
                        std::slice::from_ref(if name == "each_key" { key } else { value })
                    } else {
                        // A hash block receives the key and value. Build a
                        // temporary owned vector to keep this helper simple.
                        let expected = vec![key.clone(), value.clone()];
                        return self.eval_hash_each_block(
                            block,
                            &expected,
                            environment,
                            Type::Hash(Box::new(key.clone()), Box::new(value.clone())),
                        );
                    };
                    let _ = self.eval_block_node(block, params, environment);
                }
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "merge" | "merge!" | "update" | "reverse_merge" => {
                let mut merged_key = key.clone();
                let mut merged_value = value.clone();
                for argument in site.argument_types {
                    match argument {
                        Type::Hash(argument_key, argument_value) => {
                            merged_key = merged_key.join(argument_key);
                            merged_value = merged_value.join(argument_value);
                        }
                        Type::Any => {
                            merged_key = Type::Any;
                            merged_value = Type::Any;
                        }
                        _ => {}
                    }
                }
                if let Some(block) = site.block {
                    let block_type = self.eval_block_node(
                        block,
                        &[merged_key.clone(), value.clone(), merged_value.clone()],
                        environment,
                    );
                    merged_value = merged_value.join(&block_type);
                }
                Type::Hash(Box::new(merged_key), Box::new(merged_value))
            }
            "dup" | "clone" | "to_h" | "slice" | "except" => {
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "compact" => Type::Hash(Box::new(key.clone()), Box::new(value.without(&Type::Nil))),
            "invert" => Type::Hash(Box::new(value.clone()), Box::new(key.clone())),
            "select" | "filter" | "reject" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::Hash(Box::new(key.clone()), Box::new(value.clone()))
            }
            "any?" | "all?" | "none?" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::bool()
            }
            "sort" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::Array(Box::new(Type::Tuple(vec![key.clone(), value.clone()])))
            }
            "sort_by" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[key.clone(), value.clone()], environment);
                }
                Type::Array(Box::new(Type::Tuple(vec![key.clone(), value.clone()])))
            }
            "transform_keys" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(key), environment)
                });
                Type::Hash(Box::new(block_type), Box::new(value.clone()))
            }
            "transform_values" => {
                if site.block.is_none() {
                    return Type::named("Enumerator");
                }
                let block_type = site.block.map_or(Type::Any, |block| {
                    self.eval_block_node(block, std::slice::from_ref(value), environment)
                });
                Type::Hash(Box::new(key.clone()), Box::new(block_type))
            }
            "to_a" => Type::Array(Box::new(Type::Tuple(vec![key.clone(), value.clone()]))),
            "values_at" => Type::Array(Box::new(value.clone())),
            "length" | "size" => Type::Integer,
            "empty?" | "include?" | "key?" | "has_key?" => Type::bool(),
            _ => Type::Any,
        }
    }

    fn eval_hash_each_block<'node>(
        &mut self,
        block: &Node<'node>,
        params: &[Type],
        environment: &mut Environment,
        result: Type,
    ) -> Type {
        let _ = self.eval_block_node(block, params, environment);
        result
    }

    pub(super) fn eval_string_method<'a, 'node>(
        &mut self,
        name: &str,
        site: &CallSite<'a, 'node>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "length" | "size" | "bytesize" | "count" => Type::Integer,
            "empty?" | "start_with?" | "end_with?" | "include?" => Type::bool(),
            "to_i" | "to_int" => Type::Integer,
            "to_f" => Type::Float,
            "to_r" => Type::named("Rational"),
            "to_c" => Type::named("Complex"),
            "to_sym" | "intern" => Type::Symbol,
            "split" | "chars" | "lines" | "shellsplit" => Type::Array(Box::new(Type::String)),
            "bytes" | "codepoints" => Type::Array(Box::new(Type::Integer)),
            "[]" | "slice" | "byteslice" => Type::union([Type::Nil, Type::String]),
            "match" => Type::union([Type::Nil, Type::named("MatchData")]),
            "match?" => Type::bool(),
            "=~" => Type::union([Type::Nil, Type::Integer]),
            "<=>" => {
                if site.argument_types.first() == Some(&Type::String) {
                    Type::Integer
                } else {
                    Type::union([Type::Nil, Type::Integer])
                }
            }
            "delete_prefix" | "delete_suffix" | "inspect" | "dump" | "to_str" | "shellescape"
            | "pluralize" | "singularize" | "underscore" | "classify" | "squish" => Type::String,
            "+@" => Type::String,
            "index" | "rindex" => Type::union([Type::Nil, Type::Integer]),
            "chomp!" | "chop!" => Type::union([Type::Nil, Type::String]),
            "encode" | "reverse" | "reverse!" | "strip" | "lstrip" | "rstrip" | "upcase"
            | "downcase" | "capitalize" | "swapcase" | "chomp" | "chop" | "succ" | "next"
            | "delete" | "tr" | "tr_s" | "squeeze" | "scrub" | "center" | "ljust" | "rjust"
            | "prepend" | "concat" | "replace" | "force_encoding" | "to_s" | "dup" | "clone"
            | "+" | "*" | "<<" => Type::String,
            "gsub" | "sub" => {
                if let Some(block) = site.block {
                    let _ = self.eval_block_node(block, &[Type::String], environment);
                }
                Type::String
            }
            "each_line" | "each_char" | "each_byte" | "scan" => {
                if let Some(block) = site.block {
                    let element = if name == "each_byte" {
                        Type::Integer
                    } else {
                        Type::String
                    };
                    let _ = self.eval_block_node(block, &[element], environment);
                }
                Type::String
            }
            "chr" => Type::String,
            "ord" => Type::Integer,
            _ => Type::Any,
        }
    }

    pub(super) fn eval_numeric_method(
        &mut self,
        receiver: Type,
        name: &str,
        argument_types: &[Type],
        block: Option<&Node<'_>>,
        environment: &mut Environment,
    ) -> Type {
        match name {
            "times" | "upto" | "downto" | "step" => {
                let Some(block) = block else {
                    return Type::named("Enumerator");
                };
                let _ = self.eval_block_node(block, std::slice::from_ref(&receiver), environment);
                receiver
            }
            "+@" | "-@" => receiver,
            "|" | "&" | "^" | "<<" | ">>" => {
                if receiver == Type::Integer {
                    Type::Integer
                } else {
                    Type::Any
                }
            }
            "+" | "-" | "*" | "%" => {
                if receiver == Type::Float || argument_types.contains(&Type::Float) {
                    Type::Float
                } else {
                    Type::Integer
                }
            }
            "/" => {
                if receiver == Type::Integer
                    && argument_types.iter().all(|type_| *type_ == Type::Integer)
                {
                    Type::Integer
                } else {
                    Type::Float
                }
            }
            "<" | "<=" | ">" | ">=" | "between?" | "even?" | "odd?" | "zero?" => Type::bool(),
            "finite?" | "nan?" | "real?" | "complex?" => Type::bool(),
            "infinite?" => Type::union([Type::Nil, Type::Integer]),
            "abs" | "magnitude" => receiver,
            "fdiv" => Type::Float,
            "div" | "bit_length" | "numerator" | "denominator" => Type::Integer,
            "divmod" => Type::Array(Box::new(Type::Tuple(vec![Type::Integer, Type::Integer]))),
            "gcdlcm" => Type::Array(Box::new(Type::Integer)),
            "round" | "ceil" | "floor" | "truncate" => {
                if argument_types.is_empty() {
                    Type::Integer
                } else {
                    Type::Float
                }
            }
            "next" | "succ" | "pred" => receiver,
            "gcd" | "lcm" => Type::Integer,
            "digits" => Type::Array(Box::new(Type::Integer)),
            "clamp" => receiver,
            "to_f" => Type::Float,
            "to_i" | "to_int" => Type::Integer,
            "to_r" => Type::named("Rational"),
            "to_c" => Type::named("Complex"),
            "real" => receiver,
            "imag" => Type::Integer,
            "to_s" => Type::String,
            _ => Type::Any,
        }
    }

    pub(super) fn eval_common_method(&self, name: &str) -> Type {
        match name {
            "to_s" | "inspect" => Type::String,
            "to_enum" | "enum_for" => Type::named("Enumerator"),
            "id" | "object_id" | "hash" => Type::Integer,
            "respond_to?" | "frozen?" => Type::bool(),
            "nil?" | "to_a" => {
                if name == "to_a" {
                    Type::Array(Box::new(Type::Any))
                } else {
                    Type::bool()
                }
            }
            _ => Type::Any,
        }
    }
}

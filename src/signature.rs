use crate::types::Type;
use ruby_prism::{CallNode, DefNode, Node, Visit};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeywordParam {
    pub type_: Type,
    pub required: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MethodSig {
    pub params: Vec<Type>,
    /// Names from Sorbet's `params(name: Type)` form. RBS keyword parameters
    /// are stored in `keywords`; these names let the analyzer reconcile
    /// Sorbet's syntax with the actual Prism parameter shape.
    pub param_names: Vec<String>,
    pub return_type: Type,
    pub required_params: usize,
    pub accepts_rest: bool,
    pub keywords: BTreeMap<String, KeywordParam>,
    pub accepts_keyword_rest: bool,
    /// `void` is an effect/contract: calls produce Nil, but the final Ruby
    /// expression in the implementation is not checked as a return value.
    pub is_void: bool,
}

impl MethodSig {
    #[must_use]
    pub fn new(params: Vec<Type>, return_type: Type) -> Self {
        Self {
            required_params: params.len(),
            accepts_rest: false,
            accepts_keyword_rest: false,
            is_void: false,
            keywords: BTreeMap::new(),
            param_names: Vec::new(),
            params,
            return_type,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssertionKind {
    Let,
    Cast,
    Must,
    Unsafe,
    Absurd,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InlineAssertion {
    pub kind: AssertionKind,
    pub type_: Type,
    pub offset: usize,
}

#[derive(Clone, Debug, Default)]
pub struct AnnotationTable {
    /// Legacy name-keyed annotations used by the standalone parser helper.
    /// The analyzer uses `method_annotations`, which is anchored to Prism
    /// definition offsets and cannot leak between same-named methods.
    pub methods: BTreeMap<String, MethodSig>,
    /// Method signatures attached to actual Prism `def` nodes. Multiple
    /// consecutive Sorbet `sig` calls represent overloads for one definition.
    pub method_annotations: BTreeMap<usize, Vec<MethodSig>>,
    /// RBS type aliases collected from `#:` comments. The analyzer resolves
    /// these names against the lexical declaration that uses them.
    pub type_aliases: BTreeMap<String, Type>,
    pub assertions: BTreeMap<usize, InlineAssertion>,
}

#[derive(Clone, Debug)]
struct PendingSorbetSig {
    text: String,
    style: SorbetSigStyle,
    closed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SorbetSigStyle {
    Delimited,
    Block,
}

/// Collect Sorbet sig blocks and inline RBS comment forms. Ruby syntax itself
/// is always parsed by Prism, and RBS comments are always enabled.
#[must_use]
pub fn collect(source: &str) -> AnnotationTable {
    let lines = line_spans(source);
    let mut table = AnnotationTable::default();
    let mut sorbet_sig: Option<PendingSorbetSig> = None;
    let mut rbs_sig: Option<String> = None;

    for (line_number, (line_offset, line)) in lines.iter().enumerate() {
        let trimmed = line.trim();

        if let Some(pending) = sorbet_sig.as_mut() {
            if let Some(name) = definition_name(trimmed) {
                if let Some(signature) = parse_sorbet_signature(&pending.text) {
                    table.methods.insert(name, signature);
                }
                sorbet_sig = None;
            } else if pending.closed {
                if !trimmed.is_empty() && !trimmed.starts_with('#') {
                    sorbet_sig = None;
                }
            } else if pending.style == SorbetSigStyle::Block && trimmed == "end" {
                pending.text.push_str(line);
                pending.text.push('\n');
                pending.closed = true;
            } else if pending.style == SorbetSigStyle::Delimited {
                pending.text.push_str(line);
                pending.text.push('\n');
                pending.closed = delimiters_balanced(&pending.text);
            } else {
                pending.text.push_str(line);
                pending.text.push('\n');
            }
        } else if is_sorbet_sig_start(trimmed) {
            let start = trimmed.find("sig").unwrap_or(0);
            let text = trimmed[start..].to_owned();
            let style = if trimmed.starts_with("sig do") {
                SorbetSigStyle::Block
            } else {
                SorbetSigStyle::Delimited
            };
            sorbet_sig = Some(PendingSorbetSig {
                closed: style == SorbetSigStyle::Delimited && delimiters_balanced(&text),
                text,
                style,
            });
        }

        if let Some(text) = rbs_sig.as_mut() {
            if let Some(name) = definition_name(trimmed) {
                if let Some(signature) = parse_rbs_signature(text) {
                    table.methods.entry(name).or_insert(signature);
                }
                rbs_sig = None;
            } else if trimmed.starts_with("#|") {
                text.push_str(trimmed.trim_start_matches("#|").trim_start());
                text.push('\n');
            } else if trimmed.is_empty() || trimmed.starts_with('#') {
                // Blank and ordinary comments may separate an RBS
                // signature from its definition.
            } else {
                rbs_sig = None;
            }
        } else if let Some(comment) = trimmed.strip_prefix("#:") {
            let comment = comment.trim_start();
            if let Some((name, type_)) = parse_rbs_type_alias(comment) {
                table.type_aliases.insert(name, type_);
            } else {
                rbs_sig = Some(if comment.is_empty() {
                    String::new()
                } else {
                    format!("{comment}\n")
                });
            }
        }

        if let Some(hash) = rbs_comment_start(line) {
            if !line[..hash].trim().is_empty() {
                let comment = strip_comment_tail(&line[hash + 2..]);
                if !comment.is_empty() {
                    let (kind, type_text) = if let Some(rest) = comment.strip_prefix("as ") {
                        if rest.trim() == "!nil" {
                            (AssertionKind::Must, "untyped".to_owned())
                        } else if rest.trim() == "untyped" {
                            (AssertionKind::Unsafe, rest.trim().to_owned())
                        } else {
                            (AssertionKind::Cast, rest.trim().to_owned())
                        }
                    } else if comment == "absurd" {
                        (AssertionKind::Absurd, "bot".to_owned())
                    } else {
                        (AssertionKind::Let, comment.to_owned())
                    };
                    table.assertions.insert(
                        line_number,
                        InlineAssertion {
                            kind,
                            type_: parse_type(&type_text),
                            offset: line_offset + hash,
                        },
                    );
                }
            }
        }
    }

    table
}

/// Collect annotations using the already-parsed Prism tree.
///
/// The original line scanner is intentionally retained by [`collect`] as a
/// small public parsing utility. Whole-workspace analysis needs stronger
/// identity, though: Ruby code in a heredoc can contain text that looks like a
/// `sig` or `def`, and two unrelated owners commonly define the same method
/// name. This collector only pairs annotations with real Prism definitions.
#[must_use]
pub fn collect_for_ast(source: &str, root: &Node<'_>) -> AnnotationTable {
    let mut table = collect(source);
    table.methods.clear();
    table.method_annotations.clear();

    let mut nodes = AnnotationNodes::default();
    nodes.visit(root);
    nodes.definitions.sort_unstable();
    nodes
        .signatures
        .sort_unstable_by_key(|(start, end)| (*end, *start));

    let lines = line_spans(source);
    let mut definitions_by_line = BTreeMap::<usize, Vec<usize>>::new();
    let mut line_index = 0;
    for definition in &nodes.definitions {
        while line_index + 1 < lines.len() && lines[line_index + 1].0 <= *definition {
            line_index += 1;
        }
        definitions_by_line
            .entry(line_index)
            .or_default()
            .push(*definition);
    }

    let mut pending_rbs: Option<String> = None;
    for (line_number, (_, line)) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(definition) = definitions_by_line
            .get(&line_number)
            .and_then(|definitions| definitions.first())
        {
            if let Some(text) = pending_rbs.take() {
                if let Some(signature) = parse_rbs_signature(&text) {
                    table
                        .method_annotations
                        .entry(*definition)
                        .or_default()
                        .push(signature);
                }
            }
        }

        if let Some(comment) = trimmed.strip_prefix("#:") {
            let comment = comment.trim_start();
            pending_rbs = Some(if comment.is_empty() {
                String::new()
            } else {
                format!("{comment}\n")
            });
        } else if let Some(comment) = trimmed.strip_prefix("#|") {
            if let Some(text) = pending_rbs.as_mut() {
                text.push_str(comment.trim_start());
                text.push('\n');
            }
        } else if trimmed.is_empty() || trimmed.starts_with('#') {
            // Ordinary comments and blank lines may separate an RBS
            // signature from its definition.
        } else {
            // A signature-looking comment in a string/heredoc is not allowed
            // to survive the next real statement and attach to its `def`.
            pending_rbs = None;
        }
    }

    // Sorbet signatures are real calls in Prism. Pair a call with the next
    // definition only when the intervening source is trivia, which keeps
    // nested method bodies and fixture strings out of the annotation table.
    for definition in &nodes.definitions {
        let mut signatures = Vec::new();
        let mut cursor = *definition;
        for (start, end) in nodes
            .signatures
            .iter()
            .rev()
            .filter(|(_, end)| *end <= *definition)
        {
            if !only_trivia(&source.as_bytes()[*end..cursor]) {
                break;
            }
            if let Some(signature) = parse_sorbet_signature(&source[*start..*end]) {
                signatures.push(signature);
            }
            cursor = *start;
        }
        signatures.reverse();
        if !signatures.is_empty() {
            table.method_annotations.insert(*definition, signatures);
        }
    }

    table
}

#[derive(Default)]
struct AnnotationNodes {
    definitions: Vec<usize>,
    signatures: Vec<(usize, usize)>,
}

impl<'pr> Visit<'pr> for AnnotationNodes {
    fn visit_def_node(&mut self, node: &DefNode<'pr>) {
        self.definitions.push(crate::prism::span(&node.as_node()).0);
        ruby_prism::visit_def_node(self, node);
    }

    fn visit_call_node(&mut self, node: &CallNode<'pr>) {
        if node.receiver().is_none() && node.name().as_slice() == b"sig" {
            self.signatures.push(crate::prism::span(&node.as_node()));
        }
        ruby_prism::visit_call_node(self, node);
    }
}

fn only_trivia(source: &[u8]) -> bool {
    let mut index = 0;
    while index < source.len() {
        if source[index].is_ascii_whitespace() {
            index += 1;
        } else if source[index] == b'#' {
            while index < source.len() && source[index] != b'\n' {
                index += 1;
            }
        } else {
            return false;
        }
    }
    true
}

#[must_use]
pub fn parse_sorbet_signature(text: &str) -> Option<MethodSig> {
    let mut param_names = Vec::new();
    let params = extract_call(text, "params").map_or_else(Vec::new, |body| {
        split_top_level(&body, ',')
            .into_iter()
            .filter_map(|part| {
                split_top_level_colon(&part).map(|(name, ty)| {
                    param_names.push(name.trim().trim_start_matches('*').to_owned());
                    parse_type(ty)
                })
            })
            .collect()
    });

    let is_void = text.contains(".void");
    let return_type = if is_void {
        Type::Nil
    } else {
        extract_call(text, "returns").map_or(Type::Any, |body| parse_type(&body))
    };

    if text.contains("params") || text.contains("returns") || text.contains(".void") {
        let mut signature = MethodSig::new(params, return_type);
        signature.param_names = param_names;
        signature.is_void = is_void;
        Some(signature)
    } else {
        None
    }
}

/// Parse a Sorbet `T.type_alias { ... }` expression into the alias body.
#[must_use]
pub fn parse_sorbet_type_alias(text: &str) -> Option<Type> {
    let text = strip_comment_tail(text.trim());
    let marker = text.find("type_alias")?;
    let open = text[marker..].find('{')? + marker;
    let close = matching_delimiter(text, open, '{', '}')?;
    Some(parse_type(&text[open + 1..close]))
}

/// Parse an RBS type-alias comment such as `type Name = String`.
#[must_use]
pub fn parse_rbs_type_alias(text: &str) -> Option<(String, Type)> {
    let text = strip_comment_tail(text.trim()).strip_prefix("type ")?;
    let parts = split_top_level(text, '=');
    if parts.len() != 2 {
        return None;
    }
    let name = parts[0].trim().trim_start_matches("::");
    if name.is_empty() {
        return None;
    }
    Some((name.to_owned(), parse_type(&parts[1])))
}

#[must_use]
pub fn parse_rbs_signature(text: &str) -> Option<MethodSig> {
    let text = strip_comment_tail(text.trim());
    let arrow = find_top_level_arrow(text)?;
    let left = text[..arrow].trim();
    let right = text[arrow + 2..].trim();
    let left = if left.starts_with('[') {
        let close = matching_delimiter(left, 0, '[', ']')?;
        left[close + 1..].trim()
    } else {
        left
    };
    let mut required_params = 0;
    let mut accepts_rest = false;
    let mut accepts_keyword_rest = false;
    let mut keywords = BTreeMap::new();
    let params = if left.starts_with('(') {
        let close = matching_delimiter(left, 0, '(', ')')?;
        split_top_level(&left[1..close], ',')
            .into_iter()
            .filter(|part| !part.trim().is_empty())
            .filter_map(|part| {
                let trimmed = part.trim();
                if trimmed.starts_with('{') || trimmed.starts_with("?{") {
                    return None;
                }
                if trimmed.starts_with("**") {
                    accepts_keyword_rest = true;
                    return None;
                }
                if let Some((name, type_)) = split_top_level_colon(trimmed) {
                    let name = name.trim();
                    let required = !name.starts_with('?');
                    let name = name.trim_start_matches('?').to_owned();
                    if !name.is_empty() {
                        keywords.insert(
                            name,
                            KeywordParam {
                                type_: parse_type(type_),
                                required,
                            },
                        );
                    }
                    return None;
                }
                if trimmed.starts_with('*') {
                    accepts_rest = true;
                } else if !trimmed.starts_with('?') {
                    required_params += 1;
                }
                Some(parse_rbs_parameter(part))
            })
            .collect()
    } else {
        Vec::new()
    };
    let is_void = right == "void";
    Some(MethodSig {
        params,
        param_names: Vec::new(),
        return_type: parse_type(right),
        required_params,
        accepts_rest,
        keywords,
        accepts_keyword_rest,
        is_void,
    })
}

#[must_use]
pub fn parse_type(raw: &str) -> Type {
    let mut text = strip_comment_tail(raw.trim()).trim().to_owned();
    while text.starts_with('(') && text.ends_with(')') {
        if matching_delimiter(&text, 0, '(', ')') == Some(text.len() - 1) {
            text = text[1..text.len() - 1].trim().to_owned();
        } else {
            break;
        }
    }

    if text.is_empty() {
        return Type::Any;
    }

    if let Some(proc_type) = parse_rbs_proc_type(&text) {
        return proc_type;
    }

    let union = split_top_level(&text, '|');
    if union.len() > 1 {
        return Type::union(union.into_iter().map(|part| parse_type(&part)));
    }
    let intersection = split_top_level(&text, '&');
    if intersection.len() > 1 {
        return Type::intersection(intersection.into_iter().map(|part| parse_type(&part)));
    }
    let tuple = split_top_level(&text, ',');
    if tuple.len() > 1 {
        return Type::Tuple(tuple.into_iter().map(|part| parse_type(&part)).collect());
    }

    if let Some(inner) = text.strip_suffix('?') {
        return Type::union([Type::Nil, parse_type(inner)]);
    }
    if let Some(inner) = text.strip_prefix('?') {
        // RBS uses a leading ? on method parameters to mean optional, not
        // nilable. At this layer the type itself remains the inner type.
        return parse_type(inner);
    }

    if text.starts_with('[') && matching_delimiter(&text, 0, '[', ']') == Some(text.len() - 1) {
        let body = &text[1..text.len() - 1];
        return Type::Tuple(if body.trim().is_empty() {
            Vec::new()
        } else {
            split_top_level(body, ',')
                .into_iter()
                .map(|part| parse_type(&part))
                .collect()
        });
    }

    let normalized = text.trim_start_matches("::");
    let lower = normalized.to_ascii_lowercase();
    match lower.as_str() {
        "untyped" | "any" | "top" | "t.untyped" | "t.anything" => return Type::Any,
        "bot" | "bottom" | "t.noreturn" => return Type::Never,
        "t.attached_class" => return Type::AttachedClass,
        "t.self_type" | "t::self_type" => return Type::named("instance"),
        "void" => return Type::Nil,
        "nil" | "nilclass" => return Type::Nil,
        "bool" | "boolean" | "t::boolean" => return Type::bool(),
        "true" | "trueclass" => return Type::True,
        "false" | "falseclass" => return Type::False,
        "integer" => return Type::Integer,
        "float" => return Type::Float,
        "string" => return Type::String,
        "symbol" => return Type::Symbol,
        "object" => return Type::Object,
        _ => {}
    }

    if let Some(open) = text.find('(') {
        if text.ends_with(')') {
            let name = text[..open].trim().trim_start_matches("::");
            let body = &text[open + 1..text.len() - 1];
            match name {
                "T.nilable" => return Type::union([Type::Nil, parse_type(body)]),
                "T.any" => {
                    return Type::union(
                        split_top_level(body, ',')
                            .into_iter()
                            .map(|part| parse_type(&part)),
                    )
                }
                "T.all" => {
                    return Type::intersection(
                        split_top_level(body, ',')
                            .into_iter()
                            .map(|part| parse_type(&part)),
                    )
                }
                "singleton" | "T.class_of" => {
                    return Type::Named("Class".to_owned(), vec![parse_type(body)])
                }
                _ => {}
            }
        }
    }

    if normalized == "T.proc" || normalized.starts_with("T.proc.") {
        let params = extract_call(normalized, "params")
            .map(|body| {
                split_top_level(&body, ',')
                    .into_iter()
                    .filter_map(|part| {
                        split_top_level_colon(&part)
                            .map(|(_, type_)| parse_type(type_))
                            .or_else(|| Some(parse_type(&part)))
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let return_type =
            extract_call(normalized, "returns").map_or(Type::Any, |body| parse_type(&body));
        return Type::Proc(params, Box::new(return_type));
    }

    if let Some(open) = text.find('[') {
        if text.ends_with(']') && matching_delimiter(&text, open, '[', ']') == Some(text.len() - 1)
        {
            let name = text[..open].trim().trim_start_matches("::");
            let args = split_top_level(&text[open + 1..text.len() - 1], ',')
                .into_iter()
                .map(|part| parse_type(&part))
                .collect::<Vec<_>>();
            if args.len() == 1 && matches!(name, "Array" | "T::Array") {
                return Type::Array(Box::new(args[0].clone()));
            }
            if args.len() == 2 && matches!(name, "Hash" | "T::Hash") {
                return Type::Hash(Box::new(args[0].clone()), Box::new(args[1].clone()));
            }
            if name == "T::Class" {
                return Type::Named("Class".to_owned(), args);
            }
            return Type::Named(name.to_owned(), args);
        }
    }

    if normalized.starts_with("T.type_parameter") {
        return Type::TypeVar(normalized.to_owned());
    }
    if normalized == "T::Boolean" {
        return Type::bool();
    }
    if normalized == "Array" {
        return Type::Array(Box::new(Type::Any));
    }
    if normalized == "Hash" {
        return Type::Hash(Box::new(Type::Any), Box::new(Type::Any));
    }
    if normalized.len() == 1
        && normalized
            .as_bytes()
            .first()
            .is_some_and(u8::is_ascii_uppercase)
    {
        return Type::TypeVar(normalized.to_owned());
    }
    Type::Named(normalized.to_owned(), Vec::new())
}

fn parse_rbs_proc_type(text: &str) -> Option<Type> {
    let text = text.strip_prefix('^')?.trim();
    let arrow = find_top_level_arrow(text)?;
    let parameters = text[..arrow].trim();
    let parameters = if parameters.is_empty() {
        Vec::new()
    } else {
        let close = matching_delimiter(parameters, 0, '(', ')')?;
        if close != parameters.len() - 1 {
            return None;
        }
        split_top_level(&parameters[1..close], ',')
            .into_iter()
            .filter(|parameter| !parameter.trim().is_empty())
            .map(parse_rbs_parameter)
            .collect()
    };
    Some(Type::Proc(
        parameters,
        Box::new(parse_type(text[arrow + 2..].trim())),
    ))
}

fn parse_rbs_parameter(raw: String) -> Type {
    let mut text = raw.trim().to_owned();
    if text.starts_with('{') || text.starts_with("?{") {
        return Type::Proc(Vec::new(), Box::new(Type::Any));
    }
    while text.starts_with('*') || text.starts_with('?') {
        text.remove(0);
    }
    let has_complete_delimited_type = text.find(['[', '(', '{']).is_some_and(|open| {
        let end = match text.as_bytes()[open] as char {
            '[' => matching_delimiter(&text, open, '[', ']'),
            '(' => matching_delimiter(&text, open, '(', ')'),
            '{' => matching_delimiter(&text, open, '{', '}'),
            _ => None,
        };
        end.is_some_and(|end| text[end + 1..].trim().is_empty())
    });
    let has_top_level_union =
        split_top_level(&text, '|').len() > 1 || split_top_level(&text, '&').len() > 1;
    if text.starts_with('[') || has_complete_delimited_type || has_top_level_union {
        return parse_type(&text);
    }
    if let Some((name, ty)) = split_top_level_colon(&text) {
        if !name.trim().is_empty() {
            return parse_type(ty);
        }
    }
    let tokens = text.split_whitespace().collect::<Vec<_>>();
    if tokens.len() > 1 {
        let name_start = text
            .char_indices()
            .rev()
            .find(|(_, character)| character.is_whitespace())
            .map_or(text.len(), |(index, _)| index);
        parse_type(text[..name_start].trim())
    } else {
        parse_type(&text)
    }
}

fn is_sorbet_sig_start(line: &str) -> bool {
    line.starts_with("sig {") || line.starts_with("sig(") || line.starts_with("sig do")
}

fn rbs_comment_start(line: &str) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut quote = None;
    let mut escaped = false;
    for (index, byte) in bytes.iter().copied().enumerate() {
        if escaped {
            escaped = false;
            continue;
        }
        if byte == b'\\' && quote.is_some() {
            escaped = true;
            continue;
        }
        if let Some(current_quote) = quote {
            if byte == current_quote {
                quote = None;
            }
        } else if byte == b'\'' || byte == b'"' {
            quote = Some(byte);
        } else if byte == b'#' && bytes.get(index + 1) == Some(&b':') {
            return Some(index);
        }
    }
    None
}

fn delimiters_balanced(text: &str) -> bool {
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut bracket = 0usize;
    let mut quote = None;
    let mut escaped = false;
    for character in text.chars() {
        if escaped {
            escaped = false;
            continue;
        }
        if character == '\\' && quote.is_some() {
            escaped = true;
            continue;
        }
        if let Some(current_quote) = quote {
            if character == current_quote {
                quote = None;
            }
            continue;
        }
        if character == '\'' || character == '"' {
            quote = Some(character);
            continue;
        }
        match character {
            '(' => paren += 1,
            ')' => paren = paren.saturating_sub(1),
            '{' => brace += 1,
            '}' => brace = brace.saturating_sub(1),
            '[' => bracket += 1,
            ']' => bracket = bracket.saturating_sub(1),
            _ => {}
        }
    }
    paren == 0 && brace == 0 && bracket == 0 && quote.is_none()
}

fn definition_name(line: &str) -> Option<String> {
    let line = line.strip_prefix("private ").unwrap_or(line);
    let line = line.strip_prefix("protected ").unwrap_or(line);
    let rest = line.strip_prefix("def ")?;
    let rest = rest.trim_start_matches("self.");
    let end = rest.find(['(', ' ', ';']).unwrap_or(rest.len());
    let name = rest[..end].trim();
    (!name.is_empty()).then(|| name.to_owned())
}

fn line_spans(source: &str) -> Vec<(usize, &str)> {
    let mut result = Vec::new();
    let mut offset = 0;
    for line in source.split_inclusive('\n') {
        result.push((offset, line.trim_end_matches('\n')));
        offset += line.len();
    }
    if source.is_empty() {
        result.push((0, ""));
    }
    result
}

fn strip_comment_tail(text: &str) -> &str {
    text.split('#').next().unwrap_or(text).trim()
}

fn extract_call(text: &str, name: &str) -> Option<String> {
    let needle = format!("{name}(");
    let start = text.find(&needle)? + needle.len() - 1;
    let close = matching_delimiter(text, start, '(', ')')?;
    Some(text[start + 1..close].to_owned())
}

fn find_top_level_arrow(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut brace = 0usize;
    for index in 0..bytes.len().saturating_sub(1) {
        match bytes[index] {
            b'(' => paren += 1,
            b')' => paren = paren.saturating_sub(1),
            b'[' => bracket += 1,
            b']' => bracket = bracket.saturating_sub(1),
            b'{' => brace += 1,
            b'}' => brace = brace.saturating_sub(1),
            b'-' if bytes[index + 1] == b'>' && paren == 0 && bracket == 0 && brace == 0 => {
                return Some(index)
            }
            _ => {}
        }
    }
    None
}

fn matching_delimiter(text: &str, start: usize, open: char, close: char) -> Option<usize> {
    let mut depth = 0usize;
    let mut quote = None;
    for (relative, character) in text[start..].char_indices() {
        let index = start + relative;
        if let Some(current_quote) = quote {
            if character == current_quote {
                quote = None;
            }
            continue;
        }
        if character == '\'' || character == '\"' {
            quote = Some(character);
        } else if character == open {
            depth += 1;
        } else if character == close {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn split_top_level(text: &str, separator: char) -> Vec<String> {
    let mut result = Vec::new();
    let mut start = 0;
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut brace = 0usize;
    let mut quote = None;
    for (index, character) in text.char_indices() {
        if let Some(current_quote) = quote {
            if character == current_quote {
                quote = None;
            }
            continue;
        }
        if character == '\'' || character == '\"' {
            quote = Some(character);
        } else {
            match character {
                '(' => paren += 1,
                ')' => paren = paren.saturating_sub(1),
                '[' => bracket += 1,
                ']' => bracket = bracket.saturating_sub(1),
                '{' => brace += 1,
                '}' => brace = brace.saturating_sub(1),
                value if value == separator && paren == 0 && bracket == 0 && brace == 0 => {
                    result.push(text[start..index].trim().to_owned());
                    start = index + character.len_utf8();
                }
                _ => {}
            }
        }
    }
    result.push(text[start..].trim().to_owned());
    result
}

fn split_top_level_colon(text: &str) -> Option<(&str, &str)> {
    let mut paren = 0usize;
    let mut bracket = 0usize;
    let mut brace = 0usize;
    for (index, character) in text.char_indices() {
        match character {
            '(' => paren += 1,
            ')' => paren = paren.saturating_sub(1),
            '[' => bracket += 1,
            ']' => bracket = bracket.saturating_sub(1),
            '{' => brace += 1,
            '}' => brace = brace.saturating_sub(1),
            ':' if paren == 0
                && bracket == 0
                && brace == 0
                && text.as_bytes().get(index.wrapping_sub(1)) != Some(&b':')
                && text.as_bytes().get(index + 1) != Some(&b':') =>
            {
                return Some((&text[..index], &text[index + 1..]))
            }
            _ => {}
        }
    }
    None
}

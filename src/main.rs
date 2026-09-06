use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::time::Instant;

use ruby_prism::{Node, Visit};

use typey::directives::{typed_mode, TypedMode};
use typey::workspace::{builtin_rbi_paths, discover_ruby_files, load_workspace_paths};
use typey::{check, check_workspace, load_workspace, CheckerConfig, UntypedOrigin};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut path = None;
    let mut debug = false;
    for argument in env::args().skip(1) {
        match argument.as_str() {
            "--help" | "-h" => {
                println!(
                    "usage: typey [OPTIONS] [PATH]\n\nPATH may be a Ruby/RBI file or a repository directory.\n\nOptions:\n    -d, --debug    print analysis progress to stderr"
                );
                return Ok(());
            }
            "-d" | "--debug" => debug = true,
            _ if path.is_none() => path = Some(argument),
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }
    let config = CheckerConfig {
        debug,
        ..CheckerConfig::default()
    };
    if let Some(path) = path {
        if fs::metadata(&path)?.is_dir() {
            let started = Instant::now();
            if debug {
                eprintln!("[typey] discovering .rb/.rbi files under {path}");
            }
            let mut paths = discover_ruby_files(Path::new(&path))?;
            paths.extend(builtin_rbi_paths()?);
            paths.sort();
            paths.dedup();
            if paths.is_empty() {
                return Err(format!("no .rb or .rbi files found below {path}").into());
            }
            if debug {
                let rbi_count = paths
                    .iter()
                    .filter(|path| {
                        path.extension().and_then(|extension| extension.to_str()) == Some("rbi")
                    })
                    .count();
                eprintln!(
                    "[typey] discovered {} files ({} .rb, {} .rbi) in {:?}",
                    paths.len(),
                    paths.len() - rbi_count,
                    rbi_count,
                    started.elapsed()
                );
                eprintln!("[typey] loading source files");
            }
            let files = load_workspace_paths(&paths)?;
            if debug {
                eprintln!(
                    "[typey] loaded {} files in {:?}",
                    files.len(),
                    started.elapsed()
                );
            }
            let result = check_workspace(&files, config);
            for diagnostic in &result.diagnostics {
                println!("{}", diagnostic.render());
            }
            if debug {
                let strict_paths = files
                    .iter()
                    .filter(|file| {
                        matches!(
                            typed_mode(&file.source),
                            Some(TypedMode::Strict | TypedMode::Strong)
                        )
                    })
                    .map(|file| file.path.clone())
                    .collect::<std::collections::BTreeSet<PathBuf>>();
                let mut untyped_by_path =
                    std::collections::BTreeMap::<PathBuf, (usize, usize)>::new();
                let mut untyped_by_origin =
                    std::collections::BTreeMap::<UntypedOrigin, usize>::new();
                let mut unique_untyped_by_origin =
                    std::collections::BTreeMap::<UntypedOrigin, usize>::new();
                let mut examples_by_origin =
                    std::collections::BTreeMap::<UntypedOrigin, Vec<String>>::new();
                let mut seen_untyped = std::collections::BTreeSet::new();
                let sources_by_path = files
                    .iter()
                    .map(|file| (file.path.clone(), file.source.as_str()))
                    .collect::<std::collections::BTreeMap<_, _>>();
                for inferred in &result.types {
                    if !strict_paths.contains(&inferred.path) || !inferred.type_.contains_any() {
                        continue;
                    }
                    let entry = untyped_by_path.entry(inferred.path.clone()).or_default();
                    entry.0 += 1;
                    if inferred.type_.is_any() {
                        entry.1 += 1;
                    }
                    let origin = inferred.untyped_origin.unwrap_or(UntypedOrigin::Propagated);
                    *untyped_by_origin.entry(origin).or_default() += 1;
                    let unique = seen_untyped.insert((
                        inferred.path.clone(),
                        inferred.start,
                        inferred.end,
                        origin,
                    ));
                    if unique {
                        *unique_untyped_by_origin.entry(origin).or_default() += 1;
                        let examples = examples_by_origin.entry(origin).or_default();
                        if examples.len() < 3 {
                            if let Some(source) = sources_by_path.get(&inferred.path) {
                                let snippet = source
                                    .get(inferred.start..inferred.end)
                                    .unwrap_or_default()
                                    .replace('\n', " ");
                                let line = source[..inferred.start.min(source.len())]
                                    .bytes()
                                    .filter(|byte| *byte == b'\n')
                                    .count()
                                    + 1;
                                examples.push(format!(
                                    "{}:{} `{}` => `{}`",
                                    inferred.path.display(),
                                    line,
                                    snippet,
                                    inferred.type_
                                ));
                            }
                        }
                    }
                }
                let total = untyped_by_path
                    .values()
                    .map(|(nested, _)| nested)
                    .sum::<usize>();
                let direct = untyped_by_path
                    .values()
                    .map(|(_, direct)| direct)
                    .sum::<usize>();
                eprintln!(
                    "[typey] strict inferred types containing T.untyped: {total} ({direct} direct) across {} files",
                    untyped_by_path.len()
                );
                let mut application_recorded_send_spans = BTreeSet::new();
                let mut application_untyped_send_spans = BTreeSet::new();
                let mut application_untyped_by_origin = BTreeMap::<UntypedOrigin, usize>::new();
                let mut application_seen_untyped = BTreeSet::new();
                let mut application_examples_by_origin =
                    BTreeMap::<UntypedOrigin, Vec<String>>::new();
                let application_call_labels = files
                    .iter()
                    .filter(|file| is_application_source(&file.path))
                    .map(|file| (file.path.clone(), syntactic_call_labels(&file.source)))
                    .collect::<BTreeMap<_, _>>();
                let mut application_fallback_calls = BTreeMap::<String, usize>::new();
                for inferred in &result.types {
                    if !is_application_source(&inferred.path) || !inferred.is_send {
                        continue;
                    }
                    let span = (inferred.path.clone(), inferred.start, inferred.end);
                    application_recorded_send_spans.insert(span.clone());
                    if inferred.type_.contains_any() {
                        if application_untyped_send_spans.insert(span) {}
                        let origin = inferred.untyped_origin.unwrap_or(UntypedOrigin::Propagated);
                        if application_seen_untyped.insert((
                            inferred.path.clone(),
                            inferred.start,
                            inferred.end,
                            origin,
                        )) {
                            *application_untyped_by_origin.entry(origin).or_default() += 1;
                            if origin == UntypedOrigin::FallbackCall {
                                let label = application_call_labels
                                    .get(&inferred.path)
                                    .and_then(|labels| labels.get(&(inferred.start, inferred.end)))
                                    .cloned()
                                    .unwrap_or_else(|| "<unknown call>".to_owned());
                                *application_fallback_calls.entry(label).or_default() += 1;
                            }
                            let examples =
                                application_examples_by_origin.entry(origin).or_default();
                            if examples.len() < 5 {
                                if let Some(source) = sources_by_path.get(&inferred.path) {
                                    let snippet = source
                                        .get(inferred.start..inferred.end)
                                        .unwrap_or_default()
                                        .replace('\n', " ");
                                    let line = source[..inferred.start.min(source.len())]
                                        .bytes()
                                        .filter(|byte| *byte == b'\n')
                                        .count()
                                        + 1;
                                    examples.push(format!(
                                        "{}:{} `{}` => `{}`",
                                        inferred.path.display(),
                                        line,
                                        snippet,
                                        inferred.type_
                                    ));
                                }
                            }
                        }
                    }
                }
                let mut application_fallback_calls =
                    application_fallback_calls.into_iter().collect::<Vec<_>>();
                application_fallback_calls
                    .sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0)));
                for (label, count) in application_fallback_calls.into_iter().take(30) {
                    eprintln!("[typey]   fallback call `{label}`: {count} unique spans");
                }
                let mut application_syntactic_send_spans = BTreeSet::new();
                for file in &files {
                    if !is_application_source(&file.path) {
                        continue;
                    }
                    for (start, end) in syntactic_send_spans(&file.source) {
                        application_syntactic_send_spans.insert((file.path.clone(), start, end));
                    }
                }
                let application_untracked_send_spans = application_syntactic_send_spans
                    .difference(&application_recorded_send_spans)
                    .cloned()
                    .collect::<BTreeSet<_>>();
                let application_total = application_syntactic_send_spans.len();
                let application_untyped = application_untyped_send_spans.len();
                let application_untracked = application_untracked_send_spans.len();
                let application_unknown = application_untyped + application_untracked;
                let application_percent = if application_total == 0 {
                    0.0
                } else {
                    application_unknown as f64 * 100.0 / application_total as f64
                };
                eprintln!(
                    "[typey] application lib send sites unknown (T.untyped or untracked): {application_unknown}/{application_total} ({application_percent:.1}%)"
                );
                eprintln!(
                    "[typey] application lib send sites containing T.untyped: {application_untyped}/{application_total}"
                );
                eprintln!(
                    "[typey] application lib send sites without a recorded type: {application_untracked}/{application_total}"
                );
                for (path, start, end) in application_untracked_send_spans.iter().take(20) {
                    if let Some(source) = sources_by_path.get(path) {
                        let line = source[..(*start).min(source.len())]
                            .bytes()
                            .filter(|byte| *byte == b'\n')
                            .count()
                            + 1;
                        let snippet = source
                            .get(*start..(*end).min(source.len()))
                            .unwrap_or_default()
                            .replace('\n', " ");
                        eprintln!(
                            "[typey]   untracked {}:{} ({} recorded nodes) `{snippet}`",
                            path.display(),
                            line,
                            result
                                .types
                                .iter()
                                .filter(|inferred| {
                                    inferred.path == *path
                                        && inferred.start == *start
                                        && inferred.end == *end
                                })
                                .count()
                        );
                    }
                }
                for (origin, count) in application_untyped_by_origin {
                    eprintln!(
                        "[typey] application lib {}: {count} unique spans",
                        untyped_origin_label(origin)
                    );
                    if let Some(examples) = application_examples_by_origin.get(&origin) {
                        for example in examples {
                            eprintln!("[typey]   application example: {example}");
                        }
                    }
                }
                let mut application_files = BTreeMap::<PathBuf, (usize, usize, usize)>::new();
                for (path, start, end) in &application_syntactic_send_spans {
                    let entry = application_files.entry(path.clone()).or_default();
                    entry.0 += 1;
                    let span = (path.clone(), *start, *end);
                    if application_untyped_send_spans.contains(&span) {
                        entry.1 += 1;
                    }
                    if application_untracked_send_spans.contains(&span) {
                        entry.2 += 1;
                    }
                }
                let mut application_files = application_files.into_iter().collect::<Vec<_>>();
                application_files.sort_by(|left, right| {
                    (right.1 .1 + right.1 .2)
                        .cmp(&(left.1 .1 + left.1 .2))
                        .then_with(|| right.1 .0.cmp(&left.1 .0))
                });
                for (path, (sends, untyped, untracked)) in application_files.into_iter().take(20) {
                    eprintln!(
                        "[typey] application lib file {}: {}/{} unknown sends ({untyped} untyped, {untracked} untracked)",
                        path.display(),
                        untyped + untracked,
                        sends
                    );
                }
                let sorbet_input_syntactic_send_spans = files
                    .iter()
                    .filter(|file| is_sorbet_input_source(&file.path))
                    .flat_map(|file| {
                        syntactic_send_spans(&file.source)
                            .into_iter()
                            .map(|(start, end)| (file.path.clone(), start, end))
                    })
                    .collect::<BTreeSet<_>>();
                let sorbet_input_recorded_send_spans = result
                    .types
                    .iter()
                    .filter(|inferred| is_sorbet_input_source(&inferred.path) && inferred.is_send)
                    .map(|inferred| (inferred.path.clone(), inferred.start, inferred.end))
                    .collect::<BTreeSet<_>>();
                eprintln!(
                    "[typey] sorbet input send sites: {} source spans, {} recorded spans",
                    sorbet_input_syntactic_send_spans.len(),
                    sorbet_input_recorded_send_spans.len()
                );
                let explicit_untyped = strict_paths
                    .iter()
                    .filter_map(|path| sources_by_path.get(path))
                    .map(|source| {
                        source.matches("T.untyped").count() + source.matches("T::untyped").count()
                    })
                    .sum::<usize>();
                let explicit_unsafe = strict_paths
                    .iter()
                    .filter_map(|path| sources_by_path.get(path))
                    .map(|source| {
                        source.matches("T.unsafe").count() + source.matches("T::unsafe").count()
                    })
                    .sum::<usize>();
                eprintln!(
                    "[typey] strict source markers: {explicit_untyped} explicit T.untyped, {explicit_unsafe} T.unsafe"
                );
                for (origin, count) in &untyped_by_origin {
                    let unique = unique_untyped_by_origin.get(origin).copied().unwrap_or(0);
                    eprintln!(
                        "[typey]   {}: {count} recorded, {unique} unique spans",
                        untyped_origin_label(*origin)
                    );
                    if let Some(examples) = examples_by_origin.get(origin) {
                        for example in examples {
                            eprintln!("[typey]     {example}");
                        }
                    }
                }
                let mut files_by_count = untyped_by_path.into_iter().collect::<Vec<_>>();
                files_by_count.sort_by(|left, right| right.1.cmp(&left.1));
                for (path, (nested, direct)) in files_by_count.into_iter().take(20) {
                    eprintln!(
                        "[typey]   {}: {nested} containing, {direct} direct",
                        path.display()
                    );
                }
                eprintln!(
                    "[typey] repository check finished in {:?}",
                    started.elapsed()
                );
            }
            if result.has_errors() {
                std::process::exit(1);
            }
        } else if Path::new(&path)
            .extension()
            .and_then(|extension| extension.to_str())
            == Some("rbi")
        {
            let files = load_workspace(Path::new(&path))?;
            let result = check_workspace(&files, config);
            for diagnostic in &result.diagnostics {
                println!("{}", diagnostic.render());
            }
            if result.has_errors() {
                std::process::exit(1);
            }
        } else {
            let source = fs::read_to_string(&path)?;
            let result = check(&source, config);
            for diagnostic in &result.diagnostics {
                println!("{}", diagnostic.render(&path));
            }
            if result.has_errors() {
                std::process::exit(1);
            }
        }
    } else {
        let mut source = String::new();
        io::stdin().read_to_string(&mut source)?;
        let result = check(&source, config);
        for diagnostic in &result.diagnostics {
            println!("{}", diagnostic.render("-"));
        }
        if result.has_errors() {
            std::process::exit(1);
        }
    }
    Ok(())
}

fn untyped_origin_label(origin: UntypedOrigin) -> &'static str {
    match origin {
        UntypedOrigin::ExplicitAnnotation => "explicit annotation",
        UntypedOrigin::Unsafe => "T.unsafe result",
        UntypedOrigin::DeclaredSignature => "declared signature",
        UntypedOrigin::InferredMethod => "inferred method",
        UntypedOrigin::FallbackCall => "fallback/unmodeled call",
        UntypedOrigin::Propagated => "propagated value",
    }
}

fn is_application_source(path: &Path) -> bool {
    path.extension().and_then(|extension| extension.to_str()) == Some("rb")
        && path
            .components()
            .any(|component| component.as_os_str() == std::ffi::OsStr::new("lib"))
}

fn is_sorbet_input_source(path: &Path) -> bool {
    if !matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("rb" | "rbi")
    ) {
        return false;
    }
    let mut saw_sorbet = false;
    path.components().any(|component| {
        let name = component.as_os_str();
        let is_sorbet_rbi = saw_sorbet && name == std::ffi::OsStr::new("rbi");
        saw_sorbet = name == std::ffi::OsStr::new("sorbet");
        is_sorbet_rbi || name == std::ffi::OsStr::new("lib")
    })
}

#[derive(Default)]
struct SyntacticSendVisitor {
    spans: BTreeSet<(usize, usize)>,
}

impl SyntacticSendVisitor {
    fn record(&mut self, node: &Node<'_>) {
        let location = node.location();
        self.spans
            .insert((location.start_offset(), location.end_offset()));
    }
}

impl<'pr> Visit<'pr> for SyntacticSendVisitor {
    fn visit_call_node(&mut self, node: &ruby_prism::CallNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_call_node(self, node);
    }

    fn visit_call_and_write_node(&mut self, node: &ruby_prism::CallAndWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_call_and_write_node(self, node);
    }

    fn visit_call_operator_write_node(&mut self, node: &ruby_prism::CallOperatorWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_call_operator_write_node(self, node);
    }

    fn visit_call_or_write_node(&mut self, node: &ruby_prism::CallOrWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_call_or_write_node(self, node);
    }

    fn visit_class_variable_operator_write_node(
        &mut self,
        node: &ruby_prism::ClassVariableOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_class_variable_operator_write_node(self, node);
    }

    fn visit_constant_operator_write_node(
        &mut self,
        node: &ruby_prism::ConstantOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_constant_operator_write_node(self, node);
    }

    fn visit_constant_path_operator_write_node(
        &mut self,
        node: &ruby_prism::ConstantPathOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_constant_path_operator_write_node(self, node);
    }

    fn visit_global_variable_operator_write_node(
        &mut self,
        node: &ruby_prism::GlobalVariableOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_global_variable_operator_write_node(self, node);
    }

    fn visit_index_and_write_node(&mut self, node: &ruby_prism::IndexAndWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_index_and_write_node(self, node);
    }

    fn visit_index_operator_write_node(&mut self, node: &ruby_prism::IndexOperatorWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_index_operator_write_node(self, node);
    }

    fn visit_index_or_write_node(&mut self, node: &ruby_prism::IndexOrWriteNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_index_or_write_node(self, node);
    }

    fn visit_instance_variable_operator_write_node(
        &mut self,
        node: &ruby_prism::InstanceVariableOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_instance_variable_operator_write_node(self, node);
    }

    fn visit_local_variable_operator_write_node(
        &mut self,
        node: &ruby_prism::LocalVariableOperatorWriteNode<'pr>,
    ) {
        self.record(&node.as_node());
        ruby_prism::visit_local_variable_operator_write_node(self, node);
    }

    fn visit_super_node(&mut self, node: &ruby_prism::SuperNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_super_node(self, node);
    }

    fn visit_forwarding_super_node(&mut self, node: &ruby_prism::ForwardingSuperNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_forwarding_super_node(self, node);
    }

    fn visit_yield_node(&mut self, node: &ruby_prism::YieldNode<'pr>) {
        self.record(&node.as_node());
        ruby_prism::visit_yield_node(self, node);
    }
}

fn syntactic_send_spans(source: &str) -> BTreeSet<(usize, usize)> {
    let parsed = ruby_prism::parse(source.as_bytes());
    let mut visitor = SyntacticSendVisitor::default();
    visitor.visit(&parsed.node());
    visitor.spans
}

#[derive(Default)]
struct SyntacticCallLabelVisitor<'src> {
    source: &'src [u8],
    labels: BTreeMap<(usize, usize), String>,
}

impl<'src> Visit<'src> for SyntacticCallLabelVisitor<'src> {
    fn visit_call_node(&mut self, node: &ruby_prism::CallNode<'src>) {
        let location = node.location();
        let receiver = node
            .receiver()
            .map(|receiver| typey::prism::text(self.source, &receiver))
            .unwrap_or_else(|| "<self>".to_owned());
        let name = typey::prism::constant_name(node.name());
        self.labels.insert(
            (location.start_offset(), location.end_offset()),
            format!("{receiver}.{name}"),
        );
        ruby_prism::visit_call_node(self, node);
    }
}

fn syntactic_call_labels(source: &str) -> BTreeMap<(usize, usize), String> {
    let parsed = ruby_prism::parse(source.as_bytes());
    let mut visitor = SyntacticCallLabelVisitor {
        source: source.as_bytes(),
        ..Default::default()
    };
    visitor.visit(&parsed.node());
    visitor.labels
}

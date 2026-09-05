use ruby_prism::{ConstantId, Location, Node};

/// A thin, source-oriented adapter around ruby-prism. Keeping this module
/// small makes the checker independent from generated Prism node internals.
#[must_use]
pub fn parse(source: &[u8]) -> ruby_prism::ParseResult<'_> {
    ruby_prism::parse(source)
}

#[must_use]
pub fn span(node: &Node<'_>) -> (usize, usize) {
    let location = node.location();
    (location.start_offset(), location.end_offset())
}

#[must_use]
pub fn text(source: &[u8], node: &Node<'_>) -> String {
    let (start, end) = span(node);
    String::from_utf8_lossy(source.get(start..end).unwrap_or_default()).into_owned()
}

#[must_use]
pub fn constant_name(id: ConstantId<'_>) -> String {
    String::from_utf8_lossy(id.as_slice()).into_owned()
}

#[must_use]
pub fn location_span(location: &Location<'_>) -> (usize, usize) {
    (location.start_offset(), location.end_offset())
}

#[must_use]
pub fn line_number(source: &[u8], offset: usize) -> usize {
    source[..offset.min(source.len())]
        .iter()
        .filter(|byte| **byte == b'\n')
        .count()
}

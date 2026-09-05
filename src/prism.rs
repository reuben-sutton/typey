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

/// A reusable source offset to line-number index. Prism locations are byte
/// offsets, while Sorbet/RBS comments are line-oriented. Building this once
/// avoids rescanning the source prefix for every visited AST node.
#[derive(Clone, Debug)]
pub struct LineMap {
    starts: Vec<usize>,
}

impl LineMap {
    #[must_use]
    pub fn new(source: &[u8]) -> Self {
        let mut starts = vec![0];
        for (offset, byte) in source.iter().enumerate() {
            if *byte == b'\n' {
                starts.push(offset + 1);
            }
        }
        Self { starts }
    }

    #[must_use]
    pub fn line_number(&self, offset: usize) -> usize {
        match self.starts.binary_search(&offset) {
            Ok(line) => line,
            Err(next_line) => next_line.saturating_sub(1),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{line_number, LineMap};

    #[test]
    fn line_map_matches_prefix_scans() {
        let source = b"one\ntwo\nthree";
        let map = LineMap::new(source);
        for offset in 0..=source.len() + 2 {
            assert_eq!(map.line_number(offset), line_number(source, offset));
        }
    }
}

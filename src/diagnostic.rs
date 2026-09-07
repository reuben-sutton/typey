use std::fmt;

use crate::prism::LineMap;

/// Diagnostic severity.  `Note` is still emitted as a Sorbet-compatible
/// error line because `T.reveal_type` is intentionally an assertion fixture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Note,
}

/// A source-ranged checker diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: Severity,
    pub message: String,
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Diagnostic {
    #[must_use]
    pub fn new(
        source: &[u8],
        severity: Severity,
        message: impl Into<String>,
        start: usize,
        end: usize,
    ) -> Self {
        let start = start.min(source.len());
        let end = end.max(start).min(source.len());
        let line_map = LineMap::new(source);
        Self::new_with_line_map(source, &line_map, severity, message, start, end)
    }

    #[must_use]
    pub fn new_with_line_map(
        source: &[u8],
        line_map: &LineMap,
        severity: Severity,
        message: impl Into<String>,
        start: usize,
        end: usize,
    ) -> Self {
        let start = start.min(source.len());
        let end = end.max(start).min(source.len());
        let line_index = line_map.line_number(start);
        let line_start = line_map.line_start(line_index).unwrap_or_default();
        Self {
            severity,
            message: message.into(),
            start,
            end,
            line: line_index + 1,
            column: start.saturating_sub(line_start) + 1,
        }
    }

    #[must_use]
    pub fn error(source: &[u8], message: impl Into<String>, start: usize, end: usize) -> Self {
        Self::new(source, Severity::Error, message, start, end)
    }

    #[must_use]
    pub fn error_with_line_map(
        source: &[u8],
        line_map: &LineMap,
        message: impl Into<String>,
        start: usize,
        end: usize,
    ) -> Self {
        Self::new_with_line_map(source, line_map, Severity::Error, message, start, end)
    }

    #[must_use]
    pub fn note(source: &[u8], message: impl Into<String>, start: usize, end: usize) -> Self {
        Self::new(source, Severity::Note, message, start, end)
    }

    #[must_use]
    pub fn note_with_line_map(
        source: &[u8],
        line_map: &LineMap,
        message: impl Into<String>,
        start: usize,
        end: usize,
    ) -> Self {
        Self::new_with_line_map(source, line_map, Severity::Note, message, start, end)
    }

    #[must_use]
    pub fn render(&self, path: &str) -> String {
        format!("{path}:{}:{} - {}", self.line, self.column, self.message)
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{} - {}", self.line, self.column, self.message)
    }
}

#[cfg(test)]
mod tests {
    use super::{Diagnostic, Severity};

    #[test]
    fn clamps_ranges_and_renders_source_locations() {
        let source = b"one\ntwo\n";
        let error = Diagnostic::error(source, "bad", 4, 100);
        assert_eq!(error.severity, Severity::Error);
        assert_eq!(error.start, 4);
        assert_eq!(error.end, source.len());
        assert_eq!(error.line, 2);
        assert_eq!(error.column, 1);
        assert_eq!(error.render("example.rb"), "example.rb:2:1 - bad");
        assert_eq!(error.to_string(), "2:1 - bad");

        let note = Diagnostic::note(source, "note", 100, 0);
        assert_eq!(note.severity, Severity::Note);
        assert_eq!(note.start, source.len());
        assert_eq!(note.end, source.len());
        assert_eq!(note.line, 3);
        assert_eq!(note.column, 1);
    }

    #[test]
    fn line_map_constructor_matches_source_scan() {
        let source = b"one\ntwo\nthree";
        let line_map = crate::prism::LineMap::new(source);
        for offset in 0..=source.len() {
            assert_eq!(
                Diagnostic::error(source, "bad", offset, offset),
                Diagnostic::error_with_line_map(source, &line_map, "bad", offset, offset,)
            );
        }
    }
}

use std::fmt;

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
        let mut line = 1;
        let mut column = 1;
        for byte in &source[..start] {
            if *byte == b'\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        Self {
            severity,
            message: message.into(),
            start,
            end,
            line,
            column,
        }
    }

    #[must_use]
    pub fn error(source: &[u8], message: impl Into<String>, start: usize, end: usize) -> Self {
        Self::new(source, Severity::Error, message, start, end)
    }

    #[must_use]
    pub fn note(source: &[u8], message: impl Into<String>, start: usize, end: usize) -> Self {
        Self::new(source, Severity::Note, message, start, end)
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

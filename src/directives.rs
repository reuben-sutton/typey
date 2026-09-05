/// Return whether a source buffer has Sorbet's file-level `typed: ignore`
/// sigil in its leading comment area.
///
/// Sorbet recognizes file sigils in the first twenty lines. Keeping the
/// detector line-oriented avoids treating text inside a Ruby string as a
/// directive while still allowing a shebang or encoding comment before it.
#[must_use]
pub fn is_typed_ignore(source: &str) -> bool {
    source.lines().take(20).any(|line| {
        line.trim()
            .strip_prefix("# typed:")
            .is_some_and(|mode| mode.trim() == "ignore")
    })
}

#[cfg(test)]
mod tests {
    use super::is_typed_ignore;

    #[test]
    fn recognizes_ignore_sigils_in_the_leading_comment_area() {
        assert!(is_typed_ignore("#!/usr/bin/env ruby\n# typed: ignore\n"));
        assert!(is_typed_ignore(
            "# frozen_string_literal: true\n\n# typed: ignore\n"
        ));
    }

    #[test]
    fn does_not_treat_other_sigils_or_late_text_as_ignore() {
        assert!(!is_typed_ignore("# typed: true\n"));
        assert!(!is_typed_ignore("# typed: false\n"));
        let late = format!("{}\n# typed: ignore\n", "\n".repeat(20));
        assert!(!is_typed_ignore(&late));
    }
}

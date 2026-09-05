/// Sorbet's file-level typechecking modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypedMode {
    Ignore,
    False,
    True,
    Strict,
    Strong,
}

/// Return the first valid Sorbet file-level typechecking mode in the leading
/// comment area, if the source declares one.
///
/// Sorbet recognizes file sigils in the first twenty lines. Keeping the
/// detector line-oriented avoids treating text inside a Ruby string as a
/// directive while still allowing a shebang or encoding comment before it.
#[must_use]
pub fn typed_mode(source: &str) -> Option<TypedMode> {
    let mode = source
        .lines()
        .take(20)
        .find_map(|line| line.trim().strip_prefix("# typed:").map(str::trim))?;
    match mode {
        "ignore" => Some(TypedMode::Ignore),
        "false" => Some(TypedMode::False),
        "true" => Some(TypedMode::True),
        "strict" => Some(TypedMode::Strict),
        "strong" => Some(TypedMode::Strong),
        _ => None,
    }
}

/// Return whether a source buffer has Sorbet's file-level `typed: ignore`
/// sigil in its leading comment area.
#[must_use]
pub fn is_typed_ignore(source: &str) -> bool {
    typed_mode(source) == Some(TypedMode::Ignore)
}

#[cfg(test)]
mod tests {
    use super::{is_typed_ignore, typed_mode, TypedMode};

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

    #[test]
    fn recognizes_all_valid_sorbet_modes() {
        for (text, expected) in [
            ("ignore", TypedMode::Ignore),
            ("false", TypedMode::False),
            ("true", TypedMode::True),
            ("strict", TypedMode::Strict),
            ("strong", TypedMode::Strong),
        ] {
            assert_eq!(typed_mode(&format!("# typed: {text}\n")), Some(expected));
        }
    }

    #[test]
    fn ignores_invalid_modes_and_text_outside_the_leading_comment_area() {
        assert_eq!(typed_mode("# typed: maybe\n"), None);
        assert_eq!(typed_mode("# typed: maybe\n# typed: strict\n"), None);
        let late = format!("{}\n# typed: true\n", "\n".repeat(20));
        assert_eq!(typed_mode(&late), None);
    }
}

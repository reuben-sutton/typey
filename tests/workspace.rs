use std::path::Path;
use std::process::Command;

use typey::workspace::is_ruby_source;
use typey::{check_workspace, discover_ruby_files, load_workspace, CheckerConfig, WorkspaceFile};

const FIXTURE_ROOT: &str = "tests/workspace_repo";
const IGNORE_FIXTURE_ROOT: &str = "tests/workspace_ignore_repo";

#[test]
fn discovers_and_checks_rb_and_rbi_files_as_one_workspace() {
    let paths = discover_ruby_files(Path::new(FIXTURE_ROOT)).expect("workspace exists");
    assert_eq!(paths.len(), 3);
    assert!(paths
        .iter()
        .any(|path| path.extension().is_some_and(|ext| ext == "rb")));
    assert!(paths
        .iter()
        .any(|path| path.extension().is_some_and(|ext| ext == "rbi")));

    let files = load_workspace(Path::new(FIXTURE_ROOT)).expect("workspace loads");
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        !result.has_errors(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
    let notes = result
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.diagnostic.message.contains("Revealed type:"))
        .collect::<Vec<_>>();
    assert_eq!(notes.len(), 2, "{notes:?}");
    assert!(notes.iter().all(|diagnostic| diagnostic
        .path
        .ends_with("tests/workspace_repo/app/consumer.rb")));
    assert!(notes
        .iter()
        .all(|diagnostic| diagnostic.diagnostic.message.contains("`String`")));
}

#[test]
fn discovers_files_using_sorbet_ignore_options() {
    let paths = discover_ruby_files(Path::new(IGNORE_FIXTURE_ROOT)).expect("workspace exists");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].ends_with("tests/workspace_ignore_repo/app/kept.rb"));
}

#[test]
fn directory_cli_reports_original_file_paths() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .arg(FIXTURE_ROOT)
        .output()
        .expect("typey binary runs");
    assert!(
        output.status.success(),
        "status: {:?}\nstderr: {}\nstdout: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout
            .matches("tests/workspace_repo/app/consumer.rb")
            .count(),
        2,
        "{stdout}"
    );
    assert_eq!(
        stdout.matches("Revealed type: `String`").count(),
        2,
        "{stdout}"
    );
}

#[test]
fn direct_rbi_cli_accepts_declaration_stubs() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .arg("tests/workspace_repo/sorbet/rbi/greeting.rbi")
        .output()
        .expect("typey binary runs");
    assert!(
        output.status.success(),
        "status: {:?}\nstderr: {}\nstdout: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn debug_cli_reports_progress_on_stderr() {
    let output = Command::new(env!("CARGO_BIN_EXE_typey"))
        .args(["--debug", FIXTURE_ROOT])
        .output()
        .expect("typey binary runs");
    assert!(output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("discovering .rb/.rbi files"), "{stderr}");
    assert!(
        stderr.contains("registered 2 methods, 1 classes, and 0 type aliases"),
        "{stderr}"
    );
    assert!(stderr.contains("final reporting pass"), "{stderr}");
    assert!(
        output.stdout.is_ascii(),
        "stdout should contain diagnostics only"
    );
}

#[test]
fn workspace_skips_typed_ignore_files_before_combining_source() {
    let files = vec![
        WorkspaceFile::new(
            "ignored.rb",
            "# typed: ignore\ndef broken(\n  this is not valid Ruby\n",
        ),
        WorkspaceFile::new("valid.rb", "# typed: true\nvalue = 1\n"),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        result.diagnostics.is_empty(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
}

#[test]
fn typed_false_files_keep_declarations_but_suppress_local_diagnostics() {
    let files = vec![
        WorkspaceFile::new(
            "false.rb",
            "# typed: false\nclass Api\n  extend T::Sig\n\n  sig { params(value: Integer).void }\n  def self.accept(value); end\nend\n\nApi.accept(\"wrong\")\n",
        ),
        WorkspaceFile::new(
            "caller.rb",
            "# typed: true\nApi.accept(\"wrong\")\n",
        ),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(
                |diagnostic| diagnostic.diagnostic.severity == typey::diagnostic::Severity::Error
            )
            .count(),
        1,
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
    assert_eq!(result.diagnostics[0].path, Path::new("caller.rb"));
}

#[test]
fn strict_files_accept_cross_file_inference() {
    let files = vec![
        WorkspaceFile::new(
            "strict.rb",
            "# typed: strict\ndef identity(value)\n  value\nend\n",
        ),
        WorkspaceFile::new("caller.rb", "# typed: true\nT.reveal_type(identity(1))\n"),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        !result.has_errors(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
    assert!(
        result.diagnostics.iter().any(|diagnostic| {
            diagnostic.path == Path::new("caller.rb")
                && diagnostic
                    .diagnostic
                    .message
                    .contains("Revealed type: `Integer`")
        }),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
}

#[test]
fn reports_diagnostics_against_their_original_workspace_file() {
    let files = vec![
        WorkspaceFile::new(
            "decls.rbi",
            "class Api\n  extend T::Sig\n\n  sig { params(value: Integer).void }\n  def self.accept(value); end\nend\n",
        ),
        WorkspaceFile::new("caller.rb", "Api.accept(\"wrong\")\n"),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.diagnostic.severity == typey::diagnostic::Severity::Error)
        .expect("call-site error");
    assert_eq!(diagnostic.path, Path::new("caller.rb"));
    assert!(diagnostic
        .diagnostic
        .message
        .contains("Expected `Integer`, but found `String`"));
    assert!(diagnostic.render().starts_with("caller.rb:1:"));
}

#[test]
fn resolves_qualified_constants_lexically_before_suffix_ambiguity() {
    let files = vec![
        WorkspaceFile::new(
            "caller.rb",
            r#"module Spoom
  module Cli
    module Helper
      #: (Spoom::Color) -> void
      def accept(color)
      end

      #: (String) -> String
      def blue(string)
        accept(Color::BLUE)
        string
      end
    end
  end
end
"#,
        ),
        WorkspaceFile::new(
            "colors.rb",
            r#"module Spoom
  class Color
    #: (String) -> void
    def initialize(value)
    end

    BLUE = new("blue") #: Color
  end
end
"#,
        ),
        WorkspaceFile::new(
            "thor.rbi",
            r#"class Thor::Shell::Color
end

Thor::Shell::Color::BLUE = T.let(T.unsafe(nil), String)
"#,
        ),
    ];
    let result = check_workspace(&files, CheckerConfig::default());
    assert!(
        !result.has_errors(),
        "unexpected workspace diagnostics: {:?}",
        result.diagnostics
    );
}

#[test]
fn handles_empty_and_single_file_workspace_inputs() {
    let ignored = check_workspace(
        &[WorkspaceFile::new(
            "ignored.rb",
            "# typed: ignore\nnot valid Ruby\n",
        )],
        CheckerConfig::default(),
    );
    assert!(ignored.diagnostics.is_empty());
    assert!(ignored.types.is_empty());

    assert!(is_ruby_source(Path::new("example.rb")));
    assert!(is_ruby_source(Path::new("example.rbi")));
    assert!(!is_ruby_source(Path::new("example.RB")));
    assert_eq!(
        discover_ruby_files(Path::new("tests/workspace_repo/app/consumer.rb")).unwrap(),
        vec![Path::new("tests/workspace_repo/app/consumer.rb").to_path_buf()]
    );
    assert!(discover_ruby_files(Path::new("Cargo.toml"))
        .unwrap()
        .is_empty());
}

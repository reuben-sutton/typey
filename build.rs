use std::collections::HashSet;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=tests/fixtures");

    let mut paths = Vec::new();
    collect_fixtures(Path::new("tests/fixtures"), &mut paths)
        .expect("tests/fixtures should be readable");
    paths.sort();
    assert!(
        !paths.is_empty(),
        "the conformance suite must contain fixtures"
    );

    let mut generated = String::new();
    let mut names = HashSet::new();
    for path in paths {
        let name = test_name(&path);
        assert!(
            names.insert(name.clone()),
            "duplicate generated test name: {name}"
        );
        let path = path.to_string_lossy().replace('\\', "/");
        writeln!(generated, "conformance_fixture!({name}, {path:?});").unwrap();
    }

    let output = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set"))
        .join("conformance_fixtures.rs");
    fs::write(output, generated).expect("generated conformance tests should be writable");
}

fn collect_fixtures(root: &Path, paths: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(root)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_fixtures(&path, paths)?;
        } else if matches!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("rb" | "rbi")
        ) {
            paths.push(path);
        }
    }
    Ok(())
}

fn test_name(path: &Path) -> String {
    let mut name = String::from("fixture_");
    let relative = path.strip_prefix("tests/fixtures").unwrap_or(path);
    for character in relative.to_string_lossy().chars() {
        if character.is_ascii_alphanumeric() {
            name.push(character.to_ascii_lowercase());
        } else {
            name.push('_');
        }
    }
    name
}

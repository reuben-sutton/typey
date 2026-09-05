use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::Path;
use std::time::Instant;

use typey::workspace::{discover_ruby_files, load_workspace_paths};
use typey::{check, check_workspace, load_workspace, CheckerConfig};

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
            let paths = discover_ruby_files(Path::new(&path))?;
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

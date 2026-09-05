use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::Path;

use typey::{check, check_workspace, load_workspace, CheckerConfig};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut path = None;
    for argument in env::args().skip(1) {
        match argument.as_str() {
            "--help" | "-h" => {
                println!(
                    "usage: typey [PATH]\n\nPATH may be a Ruby/RBI file or a repository directory."
                );
                return Ok(());
            }
            _ if path.is_none() => path = Some(argument),
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }
    if let Some(path) = path {
        if fs::metadata(&path)?.is_dir() {
            let files = load_workspace(Path::new(&path))?;
            if files.is_empty() {
                return Err(format!("no .rb or .rbi files found below {path}").into());
            }
            let result = check_workspace(&files, CheckerConfig::default());
            for diagnostic in &result.diagnostics {
                println!("{}", diagnostic.render());
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
            let result = check_workspace(&files, CheckerConfig::default());
            for diagnostic in &result.diagnostics {
                println!("{}", diagnostic.render());
            }
            if result.has_errors() {
                std::process::exit(1);
            }
        } else {
            let source = fs::read_to_string(&path)?;
            let result = check(&source, CheckerConfig::default());
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
        let result = check(&source, CheckerConfig::default());
        for diagnostic in &result.diagnostics {
            println!("{}", diagnostic.render("-"));
        }
        if result.has_errors() {
            std::process::exit(1);
        }
    }
    Ok(())
}

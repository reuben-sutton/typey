use std::env;
use std::fs;
use std::io::{self, Read};

use typey::{check, CheckerConfig};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut path = None;
    for argument in env::args().skip(1) {
        match argument.as_str() {
            "--help" | "-h" => {
                println!("usage: typey [FILE]");
                return Ok(());
            }
            _ if path.is_none() => path = Some(argument),
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }
    let source = match path.as_deref() {
        Some(path) => fs::read_to_string(path)?,
        None => {
            let mut source = String::new();
            io::stdin().read_to_string(&mut source)?;
            source
        }
    };

    let result = check(&source, CheckerConfig::default());
    for diagnostic in &result.diagnostics {
        println!("{}", diagnostic.render(path.as_deref().unwrap_or("-")));
    }
    if result.has_errors() {
        std::process::exit(1);
    }
    Ok(())
}

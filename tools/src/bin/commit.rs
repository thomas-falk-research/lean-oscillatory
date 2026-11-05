#![forbid(unsafe_code)]
//! `commit DIR`, run from the Lake project root after `lake build`: runs `lake exe oscint-commit-env DIR` (the
//! environment-side producer: `DIR/statements.txt` and `DIR/<name>.env.txt`), exports the statements with
//! `leanexport` to `DIR/statements.ndjson`, computes the export-side text `DIR/<name>.export.txt`, checks the two
//! agree byte for byte, and writes `DIR/commitments.txt` (`<sha256>  <name>` lines).
//! Exit 0 on agreement, 3 when there are no statements yet (step skipped), 1 on any failure.

use oscint_tools::{canon, export::Export, sys};
use std::fs;
use std::io::BufReader;
use std::path::Path;
use std::process::Command;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 2 {
        eprintln!("usage: commit DIR");
        std::process::exit(2);
    }
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || run(&a[1])).unwrap();
    match child.join().unwrap() {
        Ok(true) => {}
        Ok(false) => {
            println!("commit: SKIPPED: no statement constants under OscInt.Statements yet");
            std::process::exit(3);
        }
        Err(e) => {
            println!("commit: FAIL: {e}");
            std::process::exit(1);
        }
    }
}

fn run(dir: &str) -> Result<bool, String> {
    let dir = Path::new(dir);
    let _ = fs::remove_dir_all(dir);
    let (ok, o, e) = sys::run(Command::new("lake").args(["exe", "oscint-commit-env"]).arg(dir))?;
    if !ok {
        return Err(format!("oscint-commit-env failed: {o}{e}"));
    }
    let stmts = fs::read_to_string(dir.join("statements.txt")).map_err(|e| format!("statements.txt: {e}"))?;
    let stmts: Vec<&str> = stmts.lines().filter(|l| !l.is_empty()).collect();
    if stmts.is_empty() {
        return Ok(false);
    }
    let export = dir.join("statements.ndjson");
    let mut args = vec!["env", "leanexport", "OscInt", "--"];
    args.extend(stmts.iter().copied());
    let res = Command::new("lake").args(&args).output().map_err(|e| e.to_string())?;
    if !res.status.success() || !res.stderr.is_empty() {
        return Err(format!("leanexport: {}", String::from_utf8_lossy(&res.stderr)));
    }
    fs::write(&export, &res.stdout).map_err(|e| e.to_string())?;
    let f = fs::File::open(&export).map_err(|e| format!("{}: {e}", export.display()))?;
    let ex = Export::read(BufReader::new(f))?;
    let mut table = String::new();
    for s in stmts {
        let txt = canon::commitment(&ex, s)?;
        let ep = dir.join(format!("{s}.export.txt"));
        fs::write(&ep, &txt).map_err(|e| e.to_string())?;
        let envp = dir.join(format!("{s}.env.txt"));
        let env = fs::read(&envp).map_err(|e| format!("{}: {e}", envp.display()))?;
        if env != txt.as_bytes() {
            let first = env
                .split(|&c| c == b'\n')
                .zip(txt.as_bytes().split(|&c| c == b'\n'))
                .position(|(x, y)| x != y);
            return Err(format!("{s}: environment and export commitments differ (first differing line {first:?})"));
        }
        let h = sys::sha256_file(&ep)?;
        println!("{h}  {s}");
        table.push_str(&format!("{h}  {s}\n"));
    }
    fs::write(dir.join("commitments.txt"), table).map_err(|e| e.to_string())?;
    Ok(true)
}

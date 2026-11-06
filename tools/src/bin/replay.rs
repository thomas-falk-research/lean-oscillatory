#![forbid(unsafe_code)]
//! `replay ROOT NAMES OUTDIR`: kernel replay of the built library. Run from the Lake project ROOT after
//! `lake build` and the axiom audit (NAMES = the audited theorem names). Steps, each recorded in
//! `OUTDIR/summary.txt` with its verdict line and duration:
//!   1. `leanchecker <Module>` for every module of the `OscInt` library;
//!   2. `leanexport OscInt -- <names>`; stderr must be empty, every name must be a theorem in the export, and
//!      the export may declare no axiom outside {propext, Classical.choice, Quot.sound};
//!   3. from that export: `leanchecker --from-export`, `leanchecker-paranoid --from-export`, `nanoda_bin`
//!      (permitted-axiom list, hard error on others), `con-leche --verified`, `con-ron --verified`, and
//!      `lake check --from-export --paranoid` (sandboxed; the only route by which this toolchain's `lean4lean`
//!      reads an export).
//! A step passes only if it exits 0, prints its acceptance line, and prints no `PANIC`/`error`/`problem`
//! (a bundled checker has been seen to report a problem and exit 0). Exit 1 on any failure.

use oscint_tools::export::{Export, Kind};
use oscint_tools::sys::{run, sha256_file};
use std::fs;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

const PERMITTED: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

fn modules(root: &Path) -> Vec<String> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<String>) {
        let Ok(rd) = fs::read_dir(dir) else { return };
        let mut v: Vec<PathBuf> = rd.flatten().map(|e| e.path()).collect();
        v.sort();
        for p in v {
            if p.is_dir() {
                walk(&p, root, out);
            } else if p.extension().is_some_and(|e| e == "lean") {
                let rel = p.strip_prefix(root).unwrap().with_extension("");
                out.push(rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join("."));
            }
        }
    }
    // The root module `OscInt` only imports; checking it re-checks every submodule in one process, which exceeded
    // 13 GB at 21 modules (OOM-killed, lessons 14). Each submodule is checked on its own instead.
    let mut out = Vec::new();
    walk(&root.join("OscInt"), root, &mut out);
    out
}

pub fn verdict(ok: bool, out: &str, accept: &str) -> Result<String, String> {
    let low = out.to_lowercase();
    for bad in ["panic", "error", "problem", "uncaught exception"] {
        if low.contains(bad) && !low.contains("no typechecker errors") {
            return Err(format!("output mentions `{bad}`"));
        }
    }
    if !ok {
        return Err("non-zero exit".into());
    }
    out.lines().find(|l| l.contains(accept)).map(|l| l.trim().to_string()).ok_or_else(|| format!("no line containing `{accept}`"))
}

pub fn check_export(ex: &Export, names: &[String]) -> Result<String, String> {
    for n in names {
        let i = ex.by_name.get(n).ok_or_else(|| format!("{n} missing from export"))?;
        if !matches!(ex.decls[*i].kind, Kind::Thm) {
            return Err(format!("{n} is not a theorem in the export"));
        }
    }
    let axioms: Vec<String> =
        ex.decls.iter().filter(|d| matches!(d.kind, Kind::Axiom { .. })).map(|d| ex.name_str(d.name)).collect();
    if let Some(a) = axioms.iter().find(|a| !PERMITTED.contains(&a.as_str())) {
        return Err(format!("export declares non-permitted axiom {a}"));
    }
    Ok(format!("{} declarations, {} target theorem(s), axioms [{}]", ex.decls.len(), names.len(), axioms.join(", ")))
}

struct Log {
    lines: Vec<String>,
    failed: bool,
}

impl Log {
    fn step(&mut self, name: &str, f: impl FnOnce() -> Result<String, String>) {
        let t = Instant::now();
        let r = f();
        let secs = t.elapsed().as_secs_f64();
        let line = match r {
            Ok(v) => format!("PASS  {name}  ({secs:.1}s)  {v}"),
            Err(e) => {
                self.failed = true;
                format!("FAIL  {name}  ({secs:.1}s)  {e}")
            }
        };
        println!("{line}");
        self.lines.push(line);
    }
}

fn lake(args: &[&str]) -> Result<(bool, String), String> {
    let (ok, o, e) = run(Command::new("lake").args(args))?;
    Ok((ok, format!("{o}{e}")))
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 4 {
        eprintln!("usage: replay ROOT NAMES OUTDIR");
        std::process::exit(2);
    }
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || go(&a[1], &a[2], &a[3])).unwrap();
    std::process::exit(child.join().unwrap());
}

fn go(root: &str, names_path: &str, outdir: &str) -> i32 {
    let root = Path::new(root);
    let out = Path::new(outdir);
    fs::create_dir_all(out).expect("outdir");
    let names: Vec<String> = fs::read_to_string(names_path)
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.is_empty())
        .map(String::from)
        .collect();
    let mut log = Log { lines: Vec::new(), failed: false };
    let sysroot = run(Command::new("lake").args(["env", "printenv", "LEAN_SYSROOT"]))
        .ok()
        .map(|(_, o, _)| o.trim().to_string())
        .unwrap_or_default();
    let commit = run(Command::new("git").args(["rev-parse", "HEAD"])).map(|r| r.1.trim().to_string()).unwrap_or_default();
    let dirty = run(Command::new("git").args(["status", "--porcelain"]))
        .map(|r| !r.1.trim().is_empty())
        .unwrap_or(true);
    let tree = run(Command::new("git").args(["rev-parse", "HEAD^{tree}"])).map(|r| r.1.trim().to_string()).unwrap_or_default();
    let mut head = vec![
        format!("commit {commit}{}", if dirty { " (working tree DIRTY: record not citable)" } else { "" }),
        format!("source tree {tree}"),
    ];
    for b in ["lean", "lake", "leanchecker", "leanchecker-paranoid", "leanexport", "nanoda_bin", "con-leche", "con-ron", "lean4lean"] {
        let p = Path::new(&sysroot).join("bin").join(b);
        head.push(format!("sha256 {} {b}", sha256_file(&p).unwrap_or_else(|e| format!("UNAVAILABLE ({e})"))));
    }
    if names.is_empty() {
        log.step("audited names", || Err(format!("{names_path} is empty or missing")));
    }
    log.step("no stale build products", || {
        let mods = modules(root);
        let mut stale = Vec::new();
        let mut oleans = Vec::new();
        fn walk(d: &Path, out: &mut Vec<PathBuf>) {
            let Ok(rd) = fs::read_dir(d) else { return };
            for p in rd.flatten().map(|e| e.path()) {
                if p.is_dir() { walk(&p, out) } else if p.extension().is_some_and(|e| e == "olean") { out.push(p) }
            }
        }
        let lib = root.join(".lake/build/lib/lean");
        walk(&lib.join("OscInt"), &mut oleans);
        for o in oleans {
            let rel = o.strip_prefix(&lib).unwrap().with_extension("");
            let m = rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect::<Vec<_>>().join(".");
            if !mods.contains(&m) {
                stale.push(m);
            }
        }
        if stale.is_empty() { Ok(format!("{} module(s)", mods.len())) } else { Err(format!("oleans without sources (leanchecker would check them): {}", stale.join(", "))) }
    });
    for m in modules(root) {
        log.step(&format!("leanchecker {m}"), || {
            let (ok, o) = lake(&["env", "leanchecker", &m])?;
            if !ok {
                return Err(format!("non-zero exit: {}", o.trim()));
            }
            verdict(ok, &format!("{o}\nexit 0"), "exit 0").map(|_| "accepted (exit 0, no error output)".into())
        });
    }
    let export = out.join("export.ndjson");
    log.step("leanexport", || {
        let mut args = vec!["env", "leanexport", "OscInt", "--"];
        args.extend(names.iter().map(String::as_str));
        let res = Command::new("lake").args(&args).output().map_err(|e| e.to_string())?;
        fs::write(&export, &res.stdout).map_err(|e| e.to_string())?;
        if !res.status.success() || !res.stderr.is_empty() {
            return Err(format!("exit {:?}, stderr: {}", res.status.code(), String::from_utf8_lossy(&res.stderr)));
        }
        let ex = Export::read(BufReader::new(fs::File::open(&export).map_err(|e| e.to_string())?))?;
        let s = check_export(&ex, &names)?;
        Ok(format!("{s}; sha256 {}", sha256_file(&export)?))
    });
    let e = export.to_string_lossy().into_owned();
    log.step("leanchecker --from-export", || {
        let (ok, o) = lake(&["env", "leanchecker", "--from-export", &e])?;
        verdict(ok, &o, "accepts the solution")
    });
    log.step("leanchecker-paranoid --from-export", || {
        let (ok, o) = lake(&["env", "leanchecker-paranoid", "--from-export", &e])?;
        verdict(ok, &o, "accepts the solution")
    });
    log.step("nanoda", || {
        let cfg = out.join("nanoda.json");
        let abs = fs::canonicalize(&export).map_err(|x| x.to_string())?;
        let body = format!(
            "{{\"export_file_path\": \"{}\", \"use_stdin\": false, \"permitted_axioms\": [\"propext\", \"Classical.choice\", \"Quot.sound\"], \"unpermitted_axiom_hard_error\": true, \"nat_extension\": true, \"string_extension\": true, \"print_success_message\": true}}",
            abs.display()
        );
        fs::write(&cfg, body).map_err(|x| x.to_string())?;
        let (ok, o) = lake(&["env", "nanoda_bin", &cfg.to_string_lossy()])?;
        // nanoda reports pretty-printer errors (no declarations requested for printing) separately from
        // type-checking errors; only the latter are verdicts.
        let low = o.to_lowercase();
        if low.contains("panic") || !ok {
            return Err(format!("nanoda failed: {}", o.trim()));
        }
        o.lines()
            .find(|l| l.contains("with no typechecker errors"))
            .map(|l| l.split(',').next().unwrap_or(l).trim().to_string())
            .ok_or_else(|| format!("no success line: {}", o.trim()))
    });
    log.step("con-leche --verified", || {
        let (ok, o) = lake(&["env", "con-leche", "--verified", &e])?;
        verdict(ok, &o, "accepted")
    });
    log.step("con-ron --verified", || {
        let (ok, o) = lake(&["env", "con-ron", "--verified", &e])?;
        verdict(ok, &o, "accepted")
    });
    log.step("lake check --from-export --paranoid", || {
        let (ok, o) = lake(&["check", "--from-export", &e, "--paranoid"])?;
        let v = verdict(ok, &o, "lean4lean kernel accepts the solution")?;
        let n = o.matches("accepts the solution").count();
        Ok(format!("{v}; {n} kernels accepted"))
    });
    let mut text = head.join("\n") + "\n";
    text += &log.lines.join("\n");
    text += &format!("\nRESULT {}\n", if log.failed { "FAIL" } else { "PASS" });
    fs::write(out.join("summary.txt"), &text).expect("summary");
    if log.failed { 1 } else { 0 }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    #[test]
    fn verdicts() {
        assert!(verdict(true, "Lean default kernel accepts the solution\n", "accepts the solution").is_ok());
        assert!(verdict(true, "lean4lean found a problem in X\n", "accepts").is_err());
        assert!(verdict(true, "PANIC at foo\naccepts the solution", "accepts").is_err());
        assert!(verdict(false, "accepts the solution", "accepts").is_err());
        assert!(verdict(true, "nothing", "accepts").is_err());
    }
    #[test]
    fn export_axiom_check() {
        let toy = "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"bad\"}}\n{\"in\":2,\"str\":{\"pre\":0,\"str\":\"t\"}}\n{\"ie\":0,\"sort\":0}\n{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n{\"thm\":{\"all\":[2],\"levelParams\":[],\"name\":2,\"type\":0,\"value\":0}}\n";
        let ex = Export::read(Cursor::new(toy)).unwrap();
        assert!(check_export(&ex, &["t".into()]).unwrap_err().contains("non-permitted axiom bad"));
        assert!(check_export(&ex, &["u".into()]).is_err());
    }
}

#![forbid(unsafe_code)]
//! `guard [--count] ROOT`: lexical tripwire over the library sources under ROOT (the repository root).
//!
//! Scans `OscInt.lean`, `OscInt/**`, `Blueprint.lean`, `Blueprint/**` (comments and literals stripped) and fails
//! on any forbidden token, on a `def <X>Statement` in `OscInt/Statements/` without its
//! `theorem statement_pin_<X>`, and on any import of the `Challenge` library. With `--count` prints only the
//! number of `theorem`/`lemma` declarations under `OscInt.lean` and `OscInt/` (compared by `audit` with the
//! number of theorems the Lean-side audit enumerates).

use oscint_tools::lexer::{find_word, strip};
use std::fs;
use std::path::{Path, PathBuf};

pub const FORBIDDEN: &[&str] = &[
    "sorry", "admit", "native_decide", "native", "axiom", "opaque", "unsafe", "implemented_by", "extern",
    "macro_rules", "macro", "notation", "infix", "infixl", "infixr", "prefix", "postfix", "syntax", "elab",
    "run_cmd", "run_meta", "run_elab", "#eval", "initialize", "debug.skipKernelTC",
];

fn lean_files(root: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = fs::read_dir(root) {
        let mut v: Vec<_> = rd.flatten().map(|e| e.path()).collect();
        v.sort();
        for p in v {
            if p.is_dir() {
                lean_files(&p, out);
            } else if p.extension().is_some_and(|e| e == "lean") {
                out.push(p);
            }
        }
    }
}

pub struct Report {
    pub violations: Vec<String>,
    pub theorems: usize,
    pub files: usize,
}

pub fn scan(root: &Path) -> Report {
    let mut files = Vec::new();
    for f in ["OscInt.lean", "Blueprint.lean"] {
        if root.join(f).exists() {
            files.push(root.join(f));
        }
    }
    lean_files(&root.join("OscInt"), &mut files);
    lean_files(&root.join("Blueprint"), &mut files);
    let mut violations = Vec::new();
    let mut theorems = 0;
    for f in &files {
        let rel = f.strip_prefix(root).unwrap_or(f).display().to_string();
        let src = match fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                violations.push(format!("{rel}: unreadable: {e}"));
                continue;
            }
        };
        violations.extend(check_source(&rel, &src));
        if rel == "OscInt.lean" || rel.starts_with("OscInt/") {
            let s = strip(&src);
            theorems += find_word(&s, "theorem").len() + find_word(&s, "lemma").len();
        }
    }
    violations.extend(check_statement_types(root));
    Report { violations, theorems, files: files.len() }
}

/// Every theorem named in a `comparator*.json` that the library declares must have an `#assert_type_is` line in
/// `StatementTypes.lean` (unproved challenge theorems are not yet in the library).
pub fn check_statement_types(root: &Path) -> Vec<String> {
    let mut cfgs: Vec<PathBuf> = fs::read_dir(root)
        .map(|rd| rd.flatten().map(|e| e.path()).collect())
        .unwrap_or_default();
    cfgs.retain(|p| p.file_name().is_some_and(|n| {
        let n = n.to_string_lossy();
        n.starts_with("comparator") && n.ends_with(".json")
    }));
    cfgs.sort();
    cfgs.iter().flat_map(|p| check_config(root, p)).collect()
}

fn check_config(root: &Path, path: &Path) -> Vec<String> {
    let Ok(cfg) = fs::read_to_string(path) else { return Vec::new() };
    let st = fs::read_to_string(root.join("StatementTypes.lean")).unwrap_or_default();
    let lib = lean_sources_text(root);
    let Ok(j) = oscint_tools::json::parse(&cfg) else { return vec!["comparator.json: not valid JSON".into()] };
    let names = j.get("theorem_names").and_then(|v| v.as_arr()).map(|a| a.to_vec()).unwrap_or_default();
    names
        .iter()
        .filter_map(|n| n.as_str())
        .filter(|n| declared(&lib, n))
        .filter(|n| !st.lines().any(|l| l.split_whitespace().take(2).eq(["#assert_type_is", n])))
        .map(|n| format!("StatementTypes.lean: no `#assert_type_is {n} …` for a declared theorem named in {}", path.display()))
        .collect()
}

/// Concatenated stripped sources of the library (`OscInt.lean`, `OscInt/**`).
fn lean_sources_text(root: &Path) -> String {
    let mut files = vec![root.join("OscInt.lean")];
    lean_files(&root.join("OscInt"), &mut files);
    files.iter().filter_map(|f| fs::read_to_string(f).ok()).map(|s| strip(&s)).collect::<Vec<_>>().join("\n")
}

/// Whether `OscInt.x` is declared as `theorem x` (inside `namespace OscInt`) or `theorem OscInt.x`.
fn declared(lib: &str, full: &str) -> bool {
    let short = full.rsplit('.').next().unwrap_or(full);
    lib.lines().any(|l| {
        let t: Vec<&str> = l.split_whitespace().collect();
        t.windows(2).any(|w| w[0] == "theorem" && (w[1] == short || w[1] == full))
    })
}

pub fn check_source(rel: &str, src: &str) -> Vec<String> {
    let s = strip(src);
    let mut v = Vec::new();
    for w in FORBIDDEN {
        for ln in find_word(&s, w) {
            v.push(format!("{rel}:{ln}: forbidden token `{w}`"));
        }
    }
    for (ln, line) in s.lines().enumerate() {
        let toks: Vec<&str> = line.split(|c: char| c.is_whitespace() || c == '[' || c == ']').filter(|t| !t.is_empty()).collect();
        if toks.windows(2).any(|w| w == ["local", "instance"]) {
            v.push(format!("{rel}:{}: forbidden `local instance`", ln + 1));
        }
        if toks.first() == Some(&"import") && toks.iter().skip(1).any(|t| *t == "Challenge" || t.starts_with("Challenge.")) {
            v.push(format!("{rel}:{}: imports the Challenge library", ln + 1));
        }
        if toks.windows(3).any(|w| w[0].trim_start_matches(['(', '@']).starts_with("ContDiff") && w[2].trim_end_matches(')') == "⊤") {
            v.push(format!("{rel}:{}: `ContDiff … ⊤` is analytic (ω) in this Mathlib; write `∞` for C^∞", ln + 1));
        }
        if toks.first() == Some(&"import") && toks.iter().skip(1).any(|t| *t == "Lean" || t.starts_with("Lean.")) {
            v.push(format!("{rel}:{}: imports Lean's metaprogramming library", ln + 1));
        }
    }
    if rel == "OscInt.lean" {
        for (ln, line) in s.lines().enumerate() {
            let t = line.trim();
            if !t.is_empty() && !t.starts_with("import ") {
                v.push(format!("{rel}:{}: the root module may only import (it is not replayed on its own)", ln + 1));
            }
        }
    }
    if rel.starts_with("OscInt/Statements/") {
        let toks: Vec<&str> = s.split_whitespace().collect();
        for w in toks.windows(2) {
            if w[0] == "def" {
                if let Some(x) = w[1].strip_suffix("Statement") {
                    let pin = format!("statement_pin_{x}");
                    let want = [ "theorem", pin.as_str(), ":", w[1], "=", w[1], ":=", "rfl" ];
                    if !toks.windows(want.len()).any(|t| t == want) {
                        v.push(format!("{rel}: `{}` has no `theorem {pin} : {} = {} := rfl`", w[1], w[1], w[1]));
                    }
                }
            }
        }
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (count, root) = match args.as_slice() {
        [r] => (false, r.clone()),
        [f, r] if f == "--count" => (true, r.clone()),
        _ => {
            eprintln!("usage: guard [--count] ROOT");
            std::process::exit(2);
        }
    };
    let rep = scan(Path::new(&root));
    if count {
        println!("{}", rep.theorems);
        return;
    }
    for v in &rep.violations {
        println!("guard: {v}");
    }
    if rep.files == 0 {
        println!("guard: FAIL: no Lean sources found under {root}");
        std::process::exit(1);
    }
    if !rep.violations.is_empty() {
        println!("guard: FAIL: {} violation(s) in {} file(s)", rep.violations.len(), rep.files);
        std::process::exit(1);
    }
    println!("guard: ok: {} file(s), 0 violations, {} theorem declaration(s)", rep.files, rep.theorems);
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn negative_controls() {
        for bad in [
            "theorem t : 1 = 1 := by sorry",
            "axiom bad : False",
            "theorem t : True := by native_decide",
            "theorem t : True := by decide +native",
            "attribute [local instance] Classical.propDecidable",
            "set_option debug.skipKernelTC true in\ntheorem t : False := x",
            "notation \"X\" => 1",
            "elab \"x\" : term => pure default",
            "import Challenge.S1",
            "import Lean.Elab.Command",
            "def P : Prop := ∀ f : ℝ → ℝ, ContDiff ℝ ⊤ f",
            "theorem t (h : ContDiffOn ℝ ⊤ f s) : True := trivial",
            "run_meta pure ()",
            "@[implemented_by f] def g := 1",
        ] {
            assert!(!check_source("OscInt/X.lean", bad).is_empty(), "missed: {bad}");
        }
    }
    #[test]
    fn positive_controls() {
        for ok in [
            "-- sorry in a comment\ntheorem t : 1 = 1 := rfl",
            "/- axiom -/ def s := \"sorry\"",
            "theorem sorryFree' : True := trivial",
        ] {
            assert!(check_source("OscInt/X.lean", ok).is_empty(), "false positive: {ok}");
        }
    }
    #[test]
    fn root_module_imports_only() {
        assert!(check_source("OscInt.lean", "import OscInt.Basic\n\nimport OscInt.X\n").is_empty());
        assert_eq!(check_source("OscInt.lean", "import OscInt.Basic\ntheorem t : True := trivial\n").len(), 1);
    }
    #[test]
    fn statement_pins() {
        let good = "def FooStatement : Prop := True\ntheorem statement_pin_Foo : FooStatement = FooStatement := rfl";
        assert!(check_source("OscInt/Statements/Foo.lean", good).is_empty());
        let bad = "def FooStatement : Prop := True";
        assert_eq!(check_source("OscInt/Statements/Foo.lean", bad).len(), 1);
    }
}

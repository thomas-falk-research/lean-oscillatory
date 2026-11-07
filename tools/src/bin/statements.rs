#![forbid(unsafe_code)]
//! `statements gen ROOT` writes `stamps/statements.json`, the machine-readable list of pinned statements that a
//! downstream project checks against (`tools/oscint_check.py`, README "Depending on OscInt"). `statements check
//! ROOT` regenerates it in memory and fails unless the committed file is byte-identical.
//!
//! Every field is derived, never typed: the statement names and stamps from `stamps/pins.txt`; the commitment, the
//! stamped commit and the statement file's SHA-256 from the pinned stamp's `manifest.txt`; the label and summary
//! from the statement's docstring in `OscInt/Statements/`; the proving theorem from `StatementTypes.lean`
//! (`#assert_type_is`); the toolchain and Mathlib revision from `lean-toolchain` and `lake-manifest.json`; and
//! `statement_files`, every file under `OscInt/Statements/` with the pinned stamp that records its hash (the files a
//! statement's closure can draw on, not only those declaring one). Generation fails if any such file has no pinned
//! stamp recording its current hash (a frozen file was edited: lessons 10). There is no package version in the
//! file, so a patch release leaves it, and a downstream pin of its SHA-256, unchanged (docs/policy.md).

use oscint_tools::{json, sys};
use std::fs;
use std::path::Path;

pub struct Entry {
    pub name: String,
    pub label: String,
    pub summary: String,
    pub file: String,
    pub file_sha256: String,
    pub commitment: String,
    pub stamp: String,
    pub stamp_commit: String,
    pub proved_by: Option<String>,
}

fn read(root: &Path, p: &str) -> Result<String, String> {
    fs::read_to_string(root.join(p)).map_err(|e| format!("{p}: {e}"))
}

/// `(statement, stamp dir)` pairs from `stamps/pins.txt`, in file order; `challenge:` lines are skipped.
pub fn pins(src: &str) -> Vec<(String, String)> {
    src.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#') && !l.starts_with("challenge:"))
        .filter_map(|l| {
            let mut it = l.split_whitespace();
            Some((it.next()?.to_string(), it.next()?.to_string()))
        })
        .collect()
}

/// The docstring immediately before `def <short> : Prop` in `src`, whitespace collapsed, if any.
pub fn docstring_of(src: &str, short: &str) -> Option<String> {
    let key = format!("def {short} : Prop");
    let at = src.find(&key)?;
    let before = src[..at].trim_end();
    let end = before.strip_suffix("-/")?;
    let start = end.rfind("/--")?;
    Some(end[start + 3..].split_whitespace().collect::<Vec<_>>().join(" "))
}

/// Splits `**S4.2** D4 limit: …` into `("S4.2", "D4 limit: …")`.
pub fn label_summary(doc: &str) -> (String, String) {
    if let Some(rest) = doc.strip_prefix("**") {
        if let Some(i) = rest.find("**") {
            return (rest[..i].to_string(), rest[i + 2..].trim().to_string());
        }
    }
    (String::new(), doc.to_string())
}

/// `statement -> theorem` from the `#assert_type_is THM STMT` lines of `StatementTypes.lean`.
pub fn proved_by(src: &str, stmt: &str) -> Option<String> {
    src.lines().find_map(|l| {
        let mut it = l.split_whitespace();
        (it.next()? == "#assert_type_is").then_some(())?;
        let thm = it.next()?;
        (it.next()? == stmt).then(|| thm.to_string())
    })
}

pub fn esc(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn manifest_field<'a>(m: &'a str, kind: &str, key: &str) -> Option<&'a str> {
    m.lines().find_map(|l| {
        let l = l.strip_prefix(kind)?.strip_prefix(' ')?;
        let (h, k) = l.split_once("  ")?;
        (k == key).then_some(h)
    })
}

fn file_hash<'a>(m: &'a str, file: &str) -> Option<&'a str> {
    m.lines().find_map(|l| {
        let (h, k) = l.split_once("  ")?;
        (k == file && h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit())).then_some(h)
    })
}

pub fn generate(root: &Path) -> Result<String, String> {
    let pins_src = read(root, "stamps/pins.txt")?;
    let types = read(root, "StatementTypes.lean")?;
    let toolchain = read(root, "lean-toolchain")?.trim().to_string();
    let manifest = json::parse(&read(root, "lake-manifest.json")?)?;
    let mathlib = manifest
        .get("packages")
        .and_then(|p| p.as_arr())
        .and_then(|ps| ps.iter().find(|p| p.get("name").and_then(|n| n.as_str()) == Some("mathlib")))
        .and_then(|p| p.get("rev"))
        .and_then(|r| r.as_str())
        .ok_or("lake-manifest.json: no mathlib package with a rev")?
        .to_string();
    let mut files: Vec<String> = fs::read_dir(root.join("OscInt/Statements"))
        .map_err(|e| format!("OscInt/Statements: {e}"))?
        .filter_map(|e| e.ok())
        .map(|e| format!("OscInt/Statements/{}", e.file_name().to_string_lossy()))
        .filter(|f| f.ends_with(".lean"))
        .collect();
    files.sort();
    let mut entries = Vec::new();
    for (name, stamp) in pins(&pins_src) {
        let short = name.strip_prefix("OscInt.Statements.").ok_or(format!("{name}: not under OscInt.Statements"))?;
        let m = read(root, &format!("{stamp}/manifest.txt"))?;
        let commitment = manifest_field(&m, "commitment", &name)
            .ok_or(format!("{stamp}/manifest.txt: no commitment line for {name}"))?
            .to_string();
        let stamp_commit = m
            .lines()
            .find_map(|l| l.strip_prefix("commit "))
            .ok_or(format!("{stamp}/manifest.txt: no commit line"))?
            .to_string();
        let mut found = None;
        for f in &files {
            if let Some(d) = docstring_of(&read(root, f)?, short) {
                found = Some((f.clone(), d));
                break;
            }
        }
        let (file, doc) = found.ok_or(format!(
            "{name}: no `def {short} : Prop` with a docstring under OscInt/Statements/ (add a `/-- **label** … -/`)"
        ))?;
        let stamped = file_hash(&m, &file).ok_or(format!("{stamp}/manifest.txt: no hash for {file}"))?;
        let now = sys::sha256_file(&root.join(&file))?;
        if now != stamped {
            return Err(format!(
                "{file} has sha256 {now} but its stamp {stamp} records {stamped}: a frozen statement file was \
                 edited. Revert it (`git checkout {stamp_commit} -- {file}`); a statement change needs a new \
                 statement, stamp, review and pin (CONTRIBUTING.md)"
            ));
        }
        let (label, summary) = label_summary(&doc);
        entries.push(Entry {
            proved_by: proved_by(&types, &name),
            name,
            label,
            summary,
            file,
            file_sha256: now,
            commitment,
            stamp,
            stamp_commit,
        });
    }
    if entries.is_empty() {
        return Err("stamps/pins.txt pins no statement".into());
    }
    let mut stamps: Vec<String> = entries.iter().map(|e| e.stamp.clone()).collect();
    stamps.sort();
    stamps.dedup();
    let mut sfiles = Vec::new();
    for f in &files {
        let now = sys::sha256_file(&root.join(f))?;
        let mut by = None;
        for st in &stamps {
            if file_hash(&read(root, &format!("{st}/manifest.txt"))?, f) == Some(now.as_str()) {
                by = Some(st.clone());
            }
        }
        let st = by.ok_or(format!(
            "{f} (sha256 {now}) is recorded by no pinned stamp: a frozen statement file was edited, or a new one \
             is not stamped yet (`make stamp`, then pin it in stamps/pins.txt)"
        ))?;
        sfiles.push((f.clone(), now, st));
    }
    Ok(render(&toolchain, &mathlib, &entries, &sfiles))
}

pub fn render(toolchain: &str, mathlib: &str, entries: &[Entry], files: &[(String, String, String)]) -> String {
    let mut o = String::new();
    o.push_str("{\n  \"format\": \"oscint-statements 1\",\n");
    o.push_str("  \"generated_by\": \"tools/src/bin/statements.rs (make statements); do not edit by hand\",\n");
    o.push_str("  \"package\": \"oscint\",\n");
    o.push_str(&format!("  \"lean_toolchain\": {},\n  \"mathlib_rev\": {},\n", esc(toolchain), esc(mathlib)));
    o.push_str("  \"statements\": [\n");
    for (i, e) in entries.iter().enumerate() {
        o.push_str("    {\n");
        o.push_str(&format!("      \"name\": {},\n", esc(&e.name)));
        o.push_str(&format!("      \"label\": {},\n", esc(&e.label)));
        o.push_str(&format!("      \"summary\": {},\n", esc(&e.summary)));
        o.push_str(&format!("      \"proved_by\": {},\n", e.proved_by.as_deref().map(esc).unwrap_or("null".into())));
        o.push_str(&format!("      \"file\": {},\n", esc(&e.file)));
        o.push_str(&format!("      \"file_sha256\": {},\n", esc(&e.file_sha256)));
        o.push_str(&format!("      \"commitment\": {},\n", esc(&e.commitment)));
        o.push_str(&format!("      \"stamp\": {},\n", esc(&e.stamp)));
        o.push_str(&format!("      \"stamp_commit\": {}\n", esc(&e.stamp_commit)));
        o.push_str(if i + 1 == entries.len() { "    }\n" } else { "    },\n" });
    }
    o.push_str("  ],\n  \"statement_files\": [\n");
    for (i, (f, h, st)) in files.iter().enumerate() {
        o.push_str(&format!(
            "    {{\"file\": {}, \"sha256\": {}, \"stamp\": {}}}{}\n",
            esc(f),
            esc(h),
            esc(st),
            if i + 1 == files.len() { "" } else { "," }
        ));
    }
    o.push_str("  ]\n}\n");
    o
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (mode, root) = match a.as_slice() {
        [_, m, r] if m == "gen" || m == "check" => (m.as_str(), Path::new(r)),
        _ => {
            eprintln!("usage: statements gen|check ROOT");
            std::process::exit(2);
        }
    };
    let out = root.join("stamps/statements.json");
    let new = match generate(root) {
        Ok(s) => s,
        Err(e) => {
            println!("statements: FAIL: {e}");
            std::process::exit(1);
        }
    };
    if mode == "gen" {
        if let Err(e) = fs::write(&out, &new) {
            println!("statements: FAIL: {}: {e}", out.display());
            std::process::exit(1);
        }
        println!("statements: wrote {} ({} statements)", out.display(), new.matches("\"name\"").count());
        return;
    }
    match fs::read_to_string(&out) {
        Ok(old) if old == new => {
            println!("statements: ok: stamps/statements.json matches pins, manifests and sources ({} statements)",
                new.matches("\"name\"").count());
        }
        Ok(_) => {
            println!("statements: FAIL: stamps/statements.json is out of date; run `make statements` and commit it");
            std::process::exit(1);
        }
        Err(e) => {
            println!("statements: FAIL: stamps/statements.json: {e}; run `make statements` and commit it");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pins_skip_comments_and_challenges() {
        let p = pins("# c\nA.B s/1\nchallenge:x.json s/1\n\nC.D s/2\n");
        assert_eq!(p, vec![("A.B".into(), "s/1".into()), ("C.D".into(), "s/2".into())]);
    }

    #[test]
    fn docstring_and_label() {
        let src = "/-- **S4.2** D4 limit:\n  `t` → c. -/\ndef XStatement : Prop :=\n  True\n";
        let d = docstring_of(src, "XStatement").unwrap();
        assert_eq!(d, "**S4.2** D4 limit: `t` → c.");
        assert_eq!(label_summary(&d), ("S4.2".into(), "D4 limit: `t` → c.".into()));
        // no docstring directly before the def: none (a comment further up must not be picked up)
        assert_eq!(docstring_of("/-- doc -/\ntheorem t : True := trivial\ndef YStatement : Prop := True", "YStatement"), None);
    }

    #[test]
    fn proved_by_matches_exact_statement() {
        let src = "#assert_type_is OscInt.a OscInt.Statements.AStatement\n#assert_type_is OscInt.b OscInt.Statements.AStatementX\n";
        assert_eq!(proved_by(src, "OscInt.Statements.AStatement"), Some("OscInt.a".into()));
        assert_eq!(proved_by(src, "OscInt.Statements.BStatement"), None);
    }

    #[test]
    fn escaping() {
        assert_eq!(esc("a\"b\\c\nd"), "\"a\\\"b\\\\c\\nd\"");
        assert_eq!(esc("Γ(1/3)²"), "\"Γ(1/3)²\"");
    }

    #[test]
    fn rendered_json_parses() {
        let e = Entry {
            name: "N".into(), label: "S1".into(), summary: "s \"q\"".into(), file: "f".into(),
            file_sha256: "h".into(), commitment: "c".into(), stamp: "st".into(), stamp_commit: "sc".into(),
            proved_by: None,
        };
        let j = json::parse(&render("t", "m", &[e], &[("f".into(), "h".into(), "st".into())])).unwrap();
        assert_eq!(j.get("mathlib_rev").and_then(|v| v.as_str()), Some("m"));
        assert!(j.get("version").is_none());
        let f = &j.get("statement_files").and_then(|s| s.as_arr()).unwrap()[0];
        assert_eq!(f.get("stamp").and_then(|v| v.as_str()), Some("st"));
        let s = &j.get("statements").and_then(|s| s.as_arr()).unwrap()[0];
        assert_eq!(s.get("summary").and_then(|v| v.as_str()), Some("s \"q\""));
    }
}

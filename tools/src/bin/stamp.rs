// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! `stamp create ROOT OUTDIR`: writes `OUTDIR/manifest.txt` (commit, then `<sha256>  <path>` for every file
//! tracked at HEAD, then the statement commitments from `build/commit/commitments.txt` and the SHA-256 of each
//! frozen challenge export in `build/challenge/` if present), obtains RFC 3161 tokens for the manifest from
//! three authorities and verifies each against its pinned root, and submits the manifest digest to two
//! OpenTimestamps calendars (pending `.ots` proofs; upgrade them later with any OpenTimestamps client).
//! Requires a clean working tree.
//! `stamp verify ROOT DIR`: re-verifies the tokens in DIR against the pinned roots and the manifest against the
//! files at the recorded commit. Exit 1 on any failure. Blobs are hashed in memory; nothing is written to DIR.
//! `stamp verify-every ROOT`: checks `stamps/pins.txt` (no duplicate key, every pinned directory exists) and then
//! verifies every stamp directory: each pinned one and every other directory under `stamps/` except `roots/`
//! (review stamps are not pinned and are verified all the same). All directories are tried; exit 1 if any fails.
//! Network and certificate work is delegated to `curl` and `openssl`; hashing to `sha256sum`.

use oscint_tools::sys::{run, sha256_bytes, sha256_file};
use std::fs;
use std::path::Path;
use std::process::Command;

/// (label, URL, pinned root file under `stamps/roots/`, SHA-256 of that file).
const TSAS: &[(&str, &str, &str, &str)] = &[
    ("freetsa", "https://freetsa.org/tsr", "freetsa.pem", "2151b61137ffa86bf664691ba67e7da0b19f98c758e3d228d5d8ebf27e044438"),
    ("digicert", "http://timestamp.digicert.com", "digicert-trusted-root-g4.pem", "ce7d6b44f5d510391be98c8d76b18709400a30cd87659bfebe1c6f97ff5181ee"),
    ("sectigo", "http://timestamp.sectigo.com", "usertrust-rsa.pem", "8a3dbcb92ab1c6277647fe2ab8536b5c982abbfdb1f1df5728e01b906aba953a"),
];
const OTS_CALENDARS: &[(&str, &str)] = &[
    ("a.pool", "https://a.pool.opentimestamps.org/digest"),
    ("b.pool", "https://b.pool.opentimestamps.org/digest"),
];
const OTS_MAGIC: &[u8] = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94";

fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    let (ok, o, e) = run(Command::new("git").arg("-C").arg(root).args(args))?;
    if !ok {
        return Err(format!("git {args:?}: {e}"));
    }
    Ok(o)
}

fn hex_decode(h: &str) -> Vec<u8> {
    (0..h.len()).step_by(2).map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap()).collect()
}

fn check_root(root: &Path, file: &str, pin: &str) -> Result<String, String> {
    let p = root.join("stamps/roots").join(file);
    let h = sha256_file(&p)?;
    if h != pin {
        return Err(format!("pinned root {file} has sha256 {h}, expected {pin}"));
    }
    Ok(p.to_string_lossy().into_owned())
}

fn verify_token(root: &Path, dir: &Path, label: &str, rootfile: &str, pin: &str) -> Result<String, String> {
    let ca = check_root(root, rootfile, pin)?;
    let tsr = dir.join(format!("{label}.tsr"));
    let (ok, o, e) = run(Command::new("openssl").args(["ts", "-verify", "-in"]).arg(&tsr).arg("-data")
        .arg(dir.join("manifest.txt")).args(["-CAfile", &ca]))?;
    if !ok || !o.contains("Verification: OK") {
        return Err(format!("{label}: verification failed: {}{}", o.trim(), e.trim()));
    }
    let (_, t, _) = run(Command::new("openssl").args(["ts", "-reply", "-text", "-in"]).arg(&tsr))?;
    let when = t.lines().find(|l| l.starts_with("Time stamp:")).unwrap_or("Time stamp: ?").trim().to_string();
    Ok(format!("{label}: Verification: OK; {when}"))
}

fn create(root: &Path, out: &Path) -> Result<(), String> {
    if !git(root, &["status", "--porcelain"])?.trim().is_empty() {
        return Err("working tree not clean; commit first".into());
    }
    let commit = git(root, &["rev-parse", "HEAD"])?.trim().to_string();
    let mut m = format!("OSCINT-MANIFEST 1\ncommit {commit}\n");
    for f in git(root, &["ls-files"])?.lines() {
        m.push_str(&format!("{}  {f}\n", sha256_file(&root.join(f))?));
    }
    let cpath = root.join("build/commit/commitments.txt");
    match fs::read_to_string(&cpath) {
        Ok(c) => {
            for l in c.lines() {
                m.push_str(&format!("commitment {l}\n"));
            }
        }
        Err(_) => m.push_str("commitment none (no statements yet)\n"),
    }
    if let Ok(rd) = fs::read_dir(root.join("build/challenge")) {
        let mut v: Vec<_> = rd.flatten().map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "ndjson")).collect();
        v.sort();
        for p in v {
            m.push_str(&format!("challenge-export {}  {}\n", sha256_file(&p)?, p.file_name().unwrap().to_string_lossy()));
        }
    }
    fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let mpath = out.join("manifest.txt");
    fs::write(&mpath, &m).map_err(|e| e.to_string())?;
    let digest = sha256_file(&mpath)?;
    println!("manifest sha256 {digest}");
    let tsq = out.join("request.tsq");
    let (ok, _, e) = run(Command::new("openssl").args(["ts", "-query", "-sha256", "-cert", "-data"]).arg(&mpath).arg("-out").arg(&tsq))?;
    if !ok {
        return Err(format!("openssl ts -query: {e}"));
    }
    let mut failures = Vec::new();
    for (label, url, rootfile, pin) in TSAS {
        let tsr = out.join(format!("{label}.tsr"));
        let (ok, code, e) = run(Command::new("curl").args(["-sS", "-m", "60", "-H", "Content-Type: application/timestamp-query", "--data-binary"])
            .arg(format!("@{}", tsq.display())).arg("-o").arg(&tsr).args(["-w", "%{http_code}", url]))?;
        if !ok || code.trim() != "200" {
            failures.push(format!("{label}: HTTP {} {e}", code.trim()));
            continue;
        }
        match verify_token(root, out, label, rootfile, pin) {
            Ok(v) => println!("{v}"),
            Err(e) => failures.push(e),
        }
    }
    let _ = fs::remove_file(&tsq);
    let dbin = out.join("digest.bin");
    fs::write(&dbin, hex_decode(&digest)).map_err(|e| e.to_string())?;
    for (label, url) in OTS_CALENDARS {
        let resp = out.join(format!("{label}.ots.resp"));
        let (ok, code, e) = run(Command::new("curl").args(["-sS", "-m", "60", "--data-binary"]).arg(format!("@{}", dbin.display()))
            .arg("-o").arg(&resp).args(["-w", "%{http_code}", url]))?;
        let body = fs::read(&resp).unwrap_or_default();
        if !ok || code.trim() != "200" || body.is_empty() || body[0] == 0xff {
            failures.push(format!("opentimestamps {label}: HTTP {} {e}", code.trim()));
            continue;
        }
        let mut ots = OTS_MAGIC.to_vec();
        ots.push(0x01);
        ots.push(0x08);
        ots.extend(hex_decode(&digest));
        ots.extend(body);
        fs::write(out.join(format!("manifest.{label}.ots")), ots).map_err(|e| e.to_string())?;
        let _ = fs::remove_file(&resp);
        println!("opentimestamps {label}: pending proof written");
    }
    let _ = fs::remove_file(&dbin);
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; "))
    }
}

/// Checks every `<sha256>  <path>` line of DIR/manifest.txt against the blob at the recorded commit (hashed in
/// memory). Returns the number of files checked.
fn verify_manifest(root: &Path, dir: &Path) -> Result<usize, String> {
    let m = fs::read_to_string(dir.join("manifest.txt")).map_err(|e| format!("manifest: {e}"))?;
    let commit = m.lines().find_map(|l| l.strip_prefix("commit ")).ok_or("manifest has no commit line")?;
    let mut n = 0;
    for l in m.lines() {
        let Some((h, path)) = l.split_once("  ") else { continue };
        if h.len() != 64 || l.starts_with("commitment") || l.starts_with("challenge-export") {
            continue;
        }
        let blob = Command::new("git").arg("-C").arg(root).args(["show", &format!("{commit}:{path}")]).output().map_err(|e| e.to_string())?;
        if !blob.status.success() {
            return Err(format!("{path} not found at {commit}"));
        }
        let got = sha256_bytes(&blob.stdout)?;
        if got != h {
            return Err(format!("{path}: sha256 at {commit} is {got}, manifest says {h}"));
        }
        n += 1;
    }
    println!("manifest: {n} file hashes match commit {commit}");
    Ok(n)
}

fn verify(root: &Path, dir: &Path) -> Result<(), String> {
    verify_manifest(root, dir)?;
    for (label, _, rootfile, pin) in TSAS {
        println!("{}", verify_token(root, dir, label, rootfile, pin)?);
    }
    for (label, _) in OTS_CALENDARS {
        let p = dir.join(format!("manifest.{label}.ots"));
        let b = fs::read(&p).map_err(|e| format!("{}: {e}", p.display()))?;
        let digest = hex_decode(&sha256_file(&dir.join("manifest.txt"))?);
        if !b.starts_with(OTS_MAGIC) || b[OTS_MAGIC.len()..OTS_MAGIC.len() + 2] != [0x01, 0x08] || b[OTS_MAGIC.len() + 2..OTS_MAGIC.len() + 34] != digest[..] {
            return Err(format!("{}: not an OpenTimestamps proof of this manifest", p.display()));
        }
        println!("opentimestamps {label}: proof file commits to the manifest digest (attestation not checked here)");
    }
    Ok(())
}

/// The stamp directories named in `stamps/pins.txt` (each once, in pin order); fails on a bad line or a duplicate
/// pin key.
fn pinned_dirs(root: &Path) -> Result<Vec<String>, String> {
    let pins = fs::read_to_string(root.join("stamps/pins.txt")).map_err(|e| format!("stamps/pins.txt: {e}"))?;
    let mut keys = Vec::new();
    let mut dirs: Vec<String> = Vec::new();
    for l in pins.lines().filter(|l| !l.starts_with('#') && !l.trim().is_empty()) {
        let (k, d) = l.split_once(' ').ok_or_else(|| format!("bad pin line: {l}"))?;
        if keys.contains(&k.to_string()) {
            return Err(format!("duplicate pin key {k} (replace the line; the last one would win silently)"));
        }
        keys.push(k.to_string());
        if !dirs.contains(&d.trim().to_string()) {
            dirs.push(d.trim().to_string());
        }
    }
    if dirs.is_empty() {
        return Err("no pinned stamps".into());
    }
    Ok(dirs)
}

/// Every directory directly under `stamps/` except `roots/`, as `stamps/<name>`, sorted. Each one is a stamp
/// directory and must verify; a directory that is not a stamp fails verification (no manifest).
fn all_stamp_dirs(root: &Path) -> Result<Vec<String>, String> {
    let rd = fs::read_dir(root.join("stamps")).map_err(|e| format!("stamps/: {e}"))?;
    let mut v = Vec::new();
    for e in rd {
        let e = e.map_err(|e| format!("stamps/: {e}"))?;
        if !e.file_type().map_err(|e| e.to_string())?.is_dir() {
            continue;
        }
        let name = e.file_name().to_string_lossy().into_owned();
        if name != "roots" {
            v.push(format!("stamps/{name}"));
        }
    }
    v.sort();
    Ok(v)
}

/// The pinned directories (in pin order) followed by every other stamp directory; fails if a pinned one is
/// missing.
fn dirs_to_verify(root: &Path) -> Result<Vec<String>, String> {
    let mut dirs = pinned_dirs(root)?;
    for d in &dirs {
        if !root.join(d).is_dir() {
            return Err(format!("pinned stamp directory {d} does not exist"));
        }
    }
    for d in all_stamp_dirs(root)? {
        if !dirs.iter().any(|p| p.trim_end_matches('/') == d) {
            dirs.push(d);
        }
    }
    Ok(dirs)
}

/// Verifies every stamp directory (`dirs_to_verify`) with `check`, trying all of them; fails if any fails.
fn verify_every_with(root: &Path, check: impl Fn(&Path, &Path) -> Result<(), String>) -> Result<(), String> {
    let pinned = pinned_dirs(root)?;
    let dirs = dirs_to_verify(root)?;
    let mut failures = Vec::new();
    for d in &dirs {
        let kind = if pinned.contains(d) { "pinned" } else { "unpinned" };
        println!("== {d} ({kind})");
        if let Err(e) = check(root, &root.join(d)) {
            println!("FAIL {d}: {e}");
            failures.push(format!("{d}: {e}"));
        }
    }
    println!("stamp directories: {} verified, {} failed", dirs.len() - failures.len(), failures.len());
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; "))
    }
}

fn verify_every(root: &Path) -> Result<(), String> {
    verify_every_with(root, verify)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let r = match a.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [_, "create", root, out] => create(Path::new(root), Path::new(out)),
        [_, "verify", root, dir] => verify(Path::new(root), Path::new(dir)),
        [_, "verify-every", root] => verify_every(Path::new(root)),
        _ => {
            eprintln!("usage: stamp create ROOT OUTDIR | stamp verify ROOT DIR | stamp verify-every ROOT");
            std::process::exit(2);
        }
    };
    if let Err(e) = r {
        println!("stamp: FAIL: {e}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn hex() {
        assert_eq!(hex_decode("00ff10"), vec![0, 255, 16]);
    }
    /// A fresh git repository in the system temp dir with `a.txt` committed; returns (root, commit).
    fn repo(tag: &str) -> (std::path::PathBuf, String) {
        let d = std::env::temp_dir().join(format!("oscint-stamp-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(d.join("stamps/roots")).unwrap();
        fs::write(d.join("a.txt"), "frozen\n").unwrap();
        let g = |args: &[&str]| {
            let o = Command::new("git")
                .arg("-C")
                .arg(&d)
                .args(["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"])
                .args(args)
                .output()
                .unwrap();
            assert!(o.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&o.stderr));
            String::from_utf8_lossy(&o.stdout).trim().to_string()
        };
        g(&["init", "-q"]);
        g(&["add", "a.txt"]);
        g(&["commit", "-q", "-m", "t"]);
        let c = g(&["rev-parse", "HEAD"]);
        (d, c)
    }
    fn write_stamp(root: &Path, name: &str, commit: &str, hash: &str) {
        let d = root.join("stamps").join(name);
        fs::create_dir_all(&d).unwrap();
        fs::write(d.join("manifest.txt"), format!("OSCINT-MANIFEST 1\ncommit {commit}\n{hash}  a.txt\n")).unwrap();
    }
    fn entries(d: &Path) -> Vec<String> {
        let mut v: Vec<String> = fs::read_dir(d).unwrap().map(|e| e.unwrap().file_name().to_string_lossy().into_owned()).collect();
        v.sort();
        v
    }
    #[test]
    fn every_directory_is_verified_pinned_first() {
        let (d, c) = repo("list");
        let good = sha256_bytes(b"frozen\n").unwrap();
        write_stamp(&d, "20260101T000000Z-bbbbbbbbbbbb", &c, &good);
        write_stamp(&d, "20260101T000000Z-aaaaaaaaaaaa", &c, &good);
        write_stamp(&d, "20260102T000000Z-cccccccccccc", &c, &good);
        fs::write(d.join("stamps/pins.txt"), "# c\nX stamps/20260101T000000Z-bbbbbbbbbbbb\nY stamps/20260101T000000Z-bbbbbbbbbbbb\n").unwrap();
        assert_eq!(
            dirs_to_verify(&d).unwrap(),
            vec!["stamps/20260101T000000Z-bbbbbbbbbbbb", "stamps/20260101T000000Z-aaaaaaaaaaaa", "stamps/20260102T000000Z-cccccccccccc"]
        );
        let _ = fs::remove_dir_all(&d);
    }
    #[test]
    fn missing_pinned_directory_is_refused() {
        let (d, _) = repo("missing");
        fs::write(d.join("stamps/pins.txt"), "X stamps/20260101T000000Z-bbbbbbbbbbbb\n").unwrap();
        assert!(dirs_to_verify(&d).unwrap_err().contains("does not exist"));
        let _ = fs::remove_dir_all(&d);
    }
    #[test]
    fn duplicate_pin_key_is_refused() {
        let (d, c) = repo("dup");
        write_stamp(&d, "P", &c, &sha256_bytes(b"frozen\n").unwrap());
        fs::write(d.join("stamps/pins.txt"), "X stamps/P\nX stamps/P\n").unwrap();
        assert!(verify_every(&d).unwrap_err().contains("duplicate pin key"));
        let _ = fs::remove_dir_all(&d);
    }
    /// Planted defect (adversarial a1): a corrupted stamp directory that no pin names must be rejected; and the
    /// manifest check must leave the stamp directories untouched (f4).
    #[test]
    fn corrupted_unpinned_stamp_is_rejected_and_nothing_is_written() {
        let (d, c) = repo("plant");
        let good = sha256_bytes(b"frozen\n").unwrap();
        let bad = format!("{}{}", if good.starts_with('0') { "1" } else { "0" }, &good[1..]);
        write_stamp(&d, "P", &c, &good);
        write_stamp(&d, "U", &c, &bad);
        fs::write(d.join("stamps/pins.txt"), "X stamps/P\n").unwrap();
        let before = (entries(&d.join("stamps/P")), entries(&d.join("stamps/U")));
        let manifest_only = |r: &Path, s: &Path| verify_manifest(r, s).map(|_| ());
        let e = verify_every_with(&d, manifest_only).unwrap_err();
        assert!(e.contains("stamps/U") && e.contains("manifest says"), "{e}");
        assert!(!e.contains("stamps/P"), "{e}");
        assert_eq!((entries(&d.join("stamps/P")), entries(&d.join("stamps/U"))), before);
        // Control: the same tree with U repaired passes.
        write_stamp(&d, "U", &c, &good);
        verify_every_with(&d, manifest_only).unwrap();
        // A directory that is not a stamp at all is unverifiable, hence rejected.
        fs::create_dir_all(d.join("stamps/stray")).unwrap();
        assert!(verify_every_with(&d, manifest_only).unwrap_err().contains("stamps/stray: manifest"));
        let _ = fs::remove_dir_all(&d);
    }
    #[test]
    fn tampered_root_is_refused() {
        let d = std::env::temp_dir().join(format!("oscint-stamp-test-{}", std::process::id()));
        fs::create_dir_all(d.join("stamps/roots")).unwrap();
        fs::write(d.join("stamps/roots/freetsa.pem"), "not the pinned root").unwrap();
        assert!(check_root(&d, "freetsa.pem", TSAS[0].3).is_err());
        let _ = fs::remove_dir_all(&d);
    }
}

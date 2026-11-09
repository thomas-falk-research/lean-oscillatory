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
//! files at the recorded commit: the manifest must be in the exact format `create` writes, its commit a full SHA
//! that is an ancestor of HEAD, and its hashed paths exactly the files of that commit. No file in DIR may be a
//! symlink. Exit 1 on any failure. Blobs are hashed in memory; nothing is written to DIR.
//! `stamp verify-every ROOT`: checks `stamps/pins.txt` (no duplicate key, every pinned directory exists) and then
//! verifies every stamp directory: each pinned one and every other directory under `stamps/` except `roots/`
//! (review stamps are not pinned and are verified all the same). Any other entry under `stamps/` (a symlink, a
//! stray file) except the regular files `pins.txt` and `statements.json` is a failure. All directories are tried;
//! exit 1 if any fails.
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

fn is_hex(s: &str, n: usize) -> bool {
    s.len() == n && s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

/// Parses a manifest in the exact format `create` writes: the header `OSCINT-MANIFEST 1`, `commit <40 hex>`, one or
/// more `<64 hex>  <path>` lines, one or more `commitment <text>` lines, then zero or more
/// `challenge-export <64 hex>  <name>` lines, in that order. Any other line (empty, malformed hash, out of order,
/// duplicate path) is an error. Returns (commit, [(hash, path)]).
fn parse_manifest(m: &str) -> Result<(String, Vec<(String, String)>), String> {
    let mut lines = m.lines();
    if lines.next() != Some("OSCINT-MANIFEST 1") {
        return Err("manifest does not start with the header `OSCINT-MANIFEST 1`".into());
    }
    let commit = lines.next().and_then(|l| l.strip_prefix("commit ")).ok_or("manifest line 2 is not `commit <sha>`")?;
    if !is_hex(commit, 40) {
        return Err(format!("manifest commit `{commit}` is not a full 40-hex SHA-1"));
    }
    // Section: 0 = file hashes, 1 = commitments, 2 = challenge exports.
    let mut section = 0;
    let mut files: Vec<(String, String)> = Vec::new();
    let mut commitments = 0;
    for (i, l) in lines.enumerate() {
        let bad = || format!("manifest line {} is malformed: `{l}`", i + 3);
        if let Some(c) = l.strip_prefix("commitment ") {
            if section > 1 || c.trim().is_empty() {
                return Err(bad());
            }
            section = 1;
            commitments += 1;
        } else if let Some(c) = l.strip_prefix("challenge-export ") {
            let (h, name) = c.split_once("  ").ok_or_else(bad)?;
            if section < 1 || !is_hex(h, 64) || name.is_empty() {
                return Err(bad());
            }
            section = 2;
        } else {
            let (h, path) = l.split_once("  ").ok_or_else(bad)?;
            if section != 0 || !is_hex(h, 64) || path.is_empty() {
                return Err(bad());
            }
            files.push((h.to_string(), path.to_string()));
        }
    }
    if files.is_empty() {
        return Err("manifest lists no file hashes".into());
    }
    if commitments == 0 {
        return Err("manifest has no commitment line".into());
    }
    let mut paths: Vec<&str> = files.iter().map(|(_, p)| p.as_str()).collect();
    paths.sort_unstable();
    if let Some(w) = paths.windows(2).find(|w| w[0] == w[1]) {
        return Err(format!("manifest lists {} twice", w[0]));
    }
    Ok((commit.to_string(), files))
}

/// Runs `git -C root args`, returning (success, stdout bytes, stderr).
fn git_raw(root: &Path, args: &[&str]) -> Result<(bool, Vec<u8>, String), String> {
    let o = Command::new("git").arg("-C").arg(root).args(args).output().map_err(|e| format!("git {args:?}: {e}"))?;
    Ok((o.status.success(), o.stdout, String::from_utf8_lossy(&o.stderr).trim().to_string()))
}

/// Checks DIR/manifest.txt: its format (`parse_manifest`); that the recorded commit exists and is an ancestor of
/// HEAD; that its hashed paths are exactly `git ls-tree -r --name-only <commit>`; and every hash against the blob at
/// that commit (hashed in memory). Returns the number of files checked.
fn verify_manifest(root: &Path, dir: &Path) -> Result<usize, String> {
    let m = fs::read_to_string(dir.join("manifest.txt")).map_err(|e| format!("manifest: {e}"))?;
    let (commit, files) = parse_manifest(&m)?;
    let commit = commit.as_str();
    if !git_raw(root, &["cat-file", "-e", &format!("{commit}^{{commit}}")])?.0 {
        return Err(format!("commit {commit} is not in this repository (a shallow clone? `git fetch --unshallow`)"));
    }
    if !git_raw(root, &["merge-base", "--is-ancestor", commit, "HEAD"])?.0 {
        return Err(format!("commit {commit} is not an ancestor of HEAD"));
    }
    let (ok, tree, e) = git_raw(root, &["ls-tree", "-r", "-z", "--name-only", commit])?;
    if !ok {
        return Err(format!("git ls-tree {commit}: {e}"));
    }
    let mut want: Vec<String> =
        tree.split(|&b| b == 0).filter(|s| !s.is_empty()).map(|s| String::from_utf8_lossy(s).into_owned()).collect();
    want.sort();
    let mut have: Vec<String> = files.iter().map(|(_, p)| p.clone()).collect();
    have.sort();
    if have != want {
        let missing: Vec<&String> = want.iter().filter(|p| have.binary_search(p).is_err()).collect();
        let extra: Vec<&String> = have.iter().filter(|p| want.binary_search(p).is_err()).collect();
        return Err(format!(
            "manifest file list differs from the tree of {commit}: {} missing {missing:?}, {} extra {extra:?}",
            missing.len(),
            extra.len()
        ));
    }
    for (h, path) in &files {
        let (ok, blob, _) = git_raw(root, &["show", &format!("{commit}:{path}")])?;
        if !ok {
            return Err(format!("{path} not found at {commit}"));
        }
        let got = sha256_bytes(&blob)?;
        if &got != h {
            return Err(format!("{path}: sha256 at {commit} is {got}, manifest says {h}"));
        }
    }
    println!("manifest: {} file hashes match commit {commit}, exactly its tracked files", files.len());
    Ok(files.len())
}

/// Checks that an `.ots` file starts with the OpenTimestamps magic, the SHA-256 op (`01 08`) and `digest`. Never
/// panics on a short or truncated file.
fn check_ots(b: &[u8], digest: &[u8]) -> Result<(), String> {
    let n = OTS_MAGIC.len();
    if !b.starts_with(OTS_MAGIC) {
        return Err("not an OpenTimestamps proof (bad magic)".into());
    }
    if b.len() < n + 2 + digest.len() {
        return Err(format!("truncated OpenTimestamps proof ({} bytes)", b.len()));
    }
    if b[n..n + 2] != [0x01, 0x08] || b[n + 2..n + 2 + digest.len()] != *digest {
        return Err("not an OpenTimestamps proof of this manifest".into());
    }
    Ok(())
}

fn verify(root: &Path, dir: &Path) -> Result<(), String> {
    let rd = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for e in rd {
        let e = e.map_err(|e| format!("{}: {e}", dir.display()))?;
        if e.file_type().map_err(|e| e.to_string())?.is_symlink() {
            return Err(format!("{} is a symbolic link; stamp files must be regular files", e.path().display()));
        }
    }
    verify_manifest(root, dir)?;
    for (label, _, rootfile, pin) in TSAS {
        println!("{}", verify_token(root, dir, label, rootfile, pin)?);
    }
    let digest = hex_decode(&sha256_file(&dir.join("manifest.txt"))?);
    for (label, _) in OTS_CALENDARS {
        let p = dir.join(format!("manifest.{label}.ots"));
        let b = fs::read(&p).map_err(|e| format!("{}: {e}", p.display()))?;
        check_ots(&b, &digest).map_err(|e| format!("{}: {e}", p.display()))?;
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

/// Classifies every entry directly under `stamps/` (file types are taken without following symlinks). Returns
/// (stamp directories as `stamps/<name>`, sorted; rejected entries as `(stamps/<name>, reason)`, sorted). The only
/// non-stamp entries allowed are the regular files `pins.txt` and `statements.json` and the real directory `roots/`;
/// every other real directory is a stamp directory and must verify; anything else (a symlink, a stray file, a
/// special file) is rejected.
fn all_stamp_dirs(root: &Path) -> Result<(Vec<String>, Vec<(String, String)>), String> {
    let rd = fs::read_dir(root.join("stamps")).map_err(|e| format!("stamps/: {e}"))?;
    let mut dirs = Vec::new();
    let mut bad = Vec::new();
    for e in rd {
        let e = e.map_err(|e| format!("stamps/: {e}"))?;
        let t = e.file_type().map_err(|e| e.to_string())?;
        let name = e.file_name().to_string_lossy().into_owned();
        let rel = format!("stamps/{name}");
        match (name.as_str(), t.is_dir(), t.is_file()) {
            ("pins.txt" | "statements.json", _, true) | ("roots", true, _) => {}
            (_, true, _) => dirs.push(rel),
            _ => {
                let what = if t.is_symlink() { "a symbolic link" } else if t.is_file() { "a stray file" } else { "not a regular file or directory" };
                bad.push((rel, format!("{what}; every entry under stamps/ other than pins.txt, statements.json and roots/ must be a real stamp directory")));
            }
        }
    }
    dirs.sort();
    bad.sort();
    Ok((dirs, bad))
}

/// The pinned directories (in pin order) followed by every other stamp directory, plus the rejected entries of
/// `all_stamp_dirs`; fails if a pinned one is not a real stamp directory directly under `stamps/`.
fn dirs_to_verify(root: &Path) -> Result<(Vec<String>, Vec<(String, String)>), String> {
    let (all, bad) = all_stamp_dirs(root)?;
    let mut dirs: Vec<String> = Vec::new();
    for d in pinned_dirs(root)? {
        let d = d.trim_end_matches('/').to_string();
        if !all.contains(&d) {
            return Err(format!("pinned stamp directory {d} does not exist (or is not a real directory directly under stamps/)"));
        }
        if !dirs.contains(&d) {
            dirs.push(d);
        }
    }
    for d in all {
        if !dirs.contains(&d) {
            dirs.push(d);
        }
    }
    Ok((dirs, bad))
}

/// Verifies every stamp directory (`dirs_to_verify`) with `check`, trying all of them; every rejected entry under
/// `stamps/` counts as a failure too. Fails if anything fails.
fn verify_every_with(root: &Path, check: impl Fn(&Path, &Path) -> Result<(), String>) -> Result<(), String> {
    let pinned: Vec<String> = pinned_dirs(root)?.iter().map(|d| d.trim_end_matches('/').to_string()).collect();
    let (dirs, bad) = dirs_to_verify(root)?;
    let mut failures = Vec::new();
    for (d, why) in &bad {
        println!("FAIL {d}: {why}");
        failures.push(format!("{d}: {why}"));
    }
    for d in &dirs {
        let kind = if pinned.contains(d) { "pinned" } else { "unpinned" };
        println!("== {d} ({kind})");
        if let Err(e) = check(root, &root.join(d)) {
            println!("FAIL {d}: {e}");
            failures.push(format!("{d}: {e}"));
        }
    }
    let failed_dirs = failures.len() - bad.len();
    println!("stamp directories: {} verified, {} failed", dirs.len() - failed_dirs, failed_dirs);
    if !bad.is_empty() {
        println!("rejected entries under stamps/: {}", bad.len());
    }
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
        fs::write(d.join("b.txt"), "second\n").unwrap();
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
        g(&["add", "a.txt", "b.txt"]);
        g(&["commit", "-q", "-m", "t"]);
        let c = g(&["rev-parse", "HEAD"]);
        (d, c)
    }
    /// A manifest in `create`'s format for the test repository, with `hash` as the hash of `a.txt`.
    fn manifest(commit: &str, hash: &str) -> String {
        let b = sha256_bytes(b"second\n").unwrap();
        format!("OSCINT-MANIFEST 1\ncommit {commit}\n{hash}  a.txt\n{b}  b.txt\ncommitment none (no statements yet)\n")
    }
    fn write_stamp(root: &Path, name: &str, commit: &str, hash: &str) {
        let d = root.join("stamps").join(name);
        fs::create_dir_all(&d).unwrap();
        fs::write(d.join("manifest.txt"), manifest(commit, hash)).unwrap();
    }
    fn manifest_only(r: &Path, s: &Path) -> Result<(), String> {
        verify_manifest(r, s).map(|_| ())
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
        let (dirs, bad) = dirs_to_verify(&d).unwrap();
        assert_eq!(
            dirs,
            vec!["stamps/20260101T000000Z-bbbbbbbbbbbb", "stamps/20260101T000000Z-aaaaaaaaaaaa", "stamps/20260102T000000Z-cccccccccccc"]
        );
        assert!(bad.is_empty(), "{bad:?}");
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
        let e =verify_every_with(&d, manifest_only).unwrap_err();
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
    /// Planted defect (adversarial m3): a symlink under stamps/ (to a valid stamp directory, to a missing target, or
    /// pinned), a stray file, or a symlinked pins.txt is a failure, never silently skipped; a symlink inside a stamp
    /// directory fails `verify`.
    #[test]
    fn symlinks_and_stray_entries_under_stamps_are_rejected() {
        use std::os::unix::fs::symlink;
        let (d, c) = repo("symlink");
        let good = sha256_bytes(b"frozen\n").unwrap();
        write_stamp(&d, "P", &c, &good);
        fs::write(d.join("stamps/pins.txt"), "X stamps/P\n").unwrap();
        fs::write(d.join("stamps/statements.json"), "{}\n").unwrap();
        verify_every_with(&d, manifest_only).unwrap(); // control
        symlink(d.join("stamps/P"), d.join("stamps/20991231T000000Z-x")).unwrap();
        let e = verify_every_with(&d, manifest_only).unwrap_err();
        assert!(e.contains("stamps/20991231T000000Z-x: a symbolic link"), "{e}");
        fs::remove_file(d.join("stamps/20991231T000000Z-x")).unwrap();
        symlink("/nonexistent-oscint-target", d.join("stamps/20991231T000000Z-y")).unwrap();
        let e = verify_every_with(&d, manifest_only).unwrap_err();
        assert!(e.contains("stamps/20991231T000000Z-y: a symbolic link"), "{e}");
        fs::remove_file(d.join("stamps/20991231T000000Z-y")).unwrap();
        fs::write(d.join("stamps/stray.txt"), "x").unwrap();
        assert!(verify_every_with(&d, manifest_only).unwrap_err().contains("stamps/stray.txt: a stray file"));
        fs::remove_file(d.join("stamps/stray.txt")).unwrap();
        // A pinned symlink is refused, not followed.
        symlink(d.join("stamps/P"), d.join("stamps/L")).unwrap();
        fs::write(d.join("stamps/pins.txt"), "X stamps/L\n").unwrap();
        assert!(verify_every_with(&d, manifest_only).unwrap_err().contains("pinned stamp directory stamps/L does not exist"));
        fs::remove_file(d.join("stamps/L")).unwrap();
        // pins.txt itself must be a regular file.
        fs::rename(d.join("stamps/pins.txt"), d.join("pins-real.txt")).unwrap();
        fs::write(d.join("pins-real.txt"), "X stamps/P\n").unwrap();
        symlink(d.join("pins-real.txt"), d.join("stamps/pins.txt")).unwrap();
        assert!(verify_every_with(&d, manifest_only).unwrap_err().contains("stamps/pins.txt: a symbolic link"));
        fs::remove_file(d.join("stamps/pins.txt")).unwrap();
        fs::write(d.join("stamps/pins.txt"), "X stamps/P\n").unwrap();
        verify_every_with(&d, manifest_only).unwrap(); // control again
        // Inside a stamp directory: `verify` refuses a symlinked file before anything else.
        symlink(d.join("a.txt"), d.join("stamps/P/freetsa.tsr")).unwrap();
        assert!(verify(&d, &d.join("stamps/P")).unwrap_err().contains("is a symbolic link"));
        let _ = fs::remove_dir_all(&d);
    }
    /// Planted defect (adversarial m4): empty, headerless, partial, malformed, padded, abbreviated-commit and
    /// non-ancestor manifests are all rejected; the well-formed manifest passes.
    #[test]
    fn defective_manifests_are_rejected() {
        let (d, c) = repo("manifest");
        let good = sha256_bytes(b"frozen\n").unwrap();
        let b = sha256_bytes(b"second\n").unwrap();
        let ok = manifest(&c, &good);
        let dir = d.join("stamps/M");
        fs::create_dir_all(&dir).unwrap();
        let check = |m: &str| {
            fs::write(dir.join("manifest.txt"), m).unwrap();
            verify_manifest(&d, &dir)
        };
        assert_eq!(check(&ok).unwrap(), 2); // control
        let g = |args: &[&str]| {
            let o = Command::new("git").arg("-C").arg(&d).args(["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]).args(args).output().unwrap();
            assert!(o.status.success());
            String::from_utf8_lossy(&o.stdout).trim().to_string()
        };
        // A commit with the same tree but no parent: exists, not an ancestor of HEAD.
        let orphan = g(&["commit-tree", "-m", "orphan", &format!("{c}^{{tree}}")]);
        let cases: Vec<(&str, String, &str)> = vec![
            ("empty", String::new(), "header"),
            ("headerless", ok.replacen("OSCINT-MANIFEST 1\n", "", 1), "header"),
            ("wrong header", ok.replacen("OSCINT-MANIFEST 1", "OSCINT-MANIFEST 2", 1), "header"),
            ("header only", format!("OSCINT-MANIFEST 1\ncommit {c}\ncommitment none\n"), "no file hashes"),
            ("partial", ok.replacen(&format!("{b}  b.txt\n"), "", 1), "missing [\"b.txt\"]"),
            ("extra path", ok.replacen("commitment", &format!("{b}  c.txt\ncommitment"), 1), "extra [\"c.txt\"]"),
            ("duplicate path", ok.replacen("commitment", &format!("{b}  b.txt\ncommitment"), 1), "twice"),
            ("short hash", ok.replacen(&format!("{b}  b.txt"), &format!("{}  b.txt", &b[1..]), 1), "malformed"),
            ("uppercase hash", ok.replacen(&format!("{b}  b.txt"), &format!("{}  b.txt", b.to_uppercase()), 1), "malformed"),
            ("garbage line", ok.replacen("commitment", "hello world\ncommitment", 1), "malformed"),
            ("blank line", ok.replacen("commitment", "\ncommitment", 1), "malformed"),
            ("hash after commitment", format!("{ok}{b}  b.txt\n"), "malformed"),
            ("no commitment", ok.replacen("commitment none (no statements yet)\n", "", 1), "no commitment"),
            ("abbreviated commit", ok.replacen(&c, &c[..12], 1), "40-hex"),
            ("unknown commit", ok.replacen(&c, &"0".repeat(40), 1), "not in this repository"),
            ("non-ancestor commit", ok.replacen(&c, &orphan, 1), "not an ancestor of HEAD"),
            ("wrong hash", manifest(&c, &b), "manifest says"),
        ];
        for (name, m, want) in cases {
            let e = check(&m).map(|n| format!("accepted ({n} files)")).unwrap_err();
            assert!(e.contains(want), "{name}: {e}");
        }
        assert_eq!(check(&ok).unwrap(), 2); // control again
        let _ = fs::remove_dir_all(&d);
    }
    /// Planted defect (adversarial n4): an `.ots` file with the magic and fewer than 34 more bytes is reported as
    /// truncated (no slice panic); every prefix of a valid proof is handled; `verify-every` goes on to the next
    /// directory.
    #[test]
    fn truncated_ots_is_reported_not_panicking() {
        let digest = hex_decode(&sha256_bytes(b"m").unwrap());
        let mut full = OTS_MAGIC.to_vec();
        full.extend([0x01, 0x08]);
        full.extend(&digest);
        full.push(0xf0);
        check_ots(&full, &digest).unwrap(); // control
        for n in 0..full.len() - 1 {
            assert!(check_ots(&full[..n], &digest).is_err(), "prefix {n} accepted");
        }
        for extra in 31..=33 {
            let e = check_ots(&full[..OTS_MAGIC.len() + extra], &digest).unwrap_err();
            assert!(e.contains("truncated"), "{e}");
        }
        let mut wrong = full.clone();
        wrong[OTS_MAGIC.len() + 5] ^= 1;
        assert!(check_ots(&wrong, &digest).unwrap_err().contains("of this manifest"));
        // verify-every reports the bad directory and still checks the next one.
        let (d, c) = repo("ots");
        let good = sha256_bytes(b"frozen\n").unwrap();
        write_stamp(&d, "A", &c, &good);
        write_stamp(&d, "B", &c, &good);
        fs::write(d.join("stamps/A/manifest.a.pool.ots"), &full[..OTS_MAGIC.len() + 32]).unwrap();
        fs::write(d.join("stamps/pins.txt"), "X stamps/A\n").unwrap();
        let seen = std::cell::RefCell::new(Vec::new());
        let ots_only = |_: &Path, s: &Path| {
            seen.borrow_mut().push(s.file_name().unwrap().to_string_lossy().into_owned());
            match fs::read(s.join("manifest.a.pool.ots")) {
                Ok(b) => check_ots(&b, &digest),
                Err(_) => Ok(()),
            }
        };
        let e = verify_every_with(&d, ots_only).unwrap_err();
        assert!(e.contains("stamps/A: truncated"), "{e}");
        assert_eq!(*seen.borrow(), vec!["A", "B"]);
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

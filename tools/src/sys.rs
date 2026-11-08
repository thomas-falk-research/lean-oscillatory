// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Process helpers. SHA-256 is computed by coreutils `sha256sum`, not reimplemented here.

use std::path::Path;
use std::process::Command;

pub fn sha256_file(p: &Path) -> Result<String, String> {
    let out = Command::new("sha256sum")
        .arg("--")
        .arg(p)
        .output()
        .map_err(|e| format!("sha256sum: {e}"))?;
    if !out.status.success() {
        return Err(format!("sha256sum failed on {}", p.display()));
    }
    let s = String::from_utf8_lossy(&out.stdout);
    let h = s.split_whitespace().next().unwrap_or("");
    if h.len() != 64 || !h.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!("unexpected sha256sum output: {s}"));
    }
    Ok(h.to_string())
}

/// SHA-256 of in-memory bytes, piped to `sha256sum` on stdin (no temporary file).
pub fn sha256_bytes(b: &[u8]) -> Result<String, String> {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("sha256sum: {e}"))?;
    // sha256sum writes nothing before EOF on stdin, so writing all input first cannot deadlock.
    child.stdin.take().ok_or("sha256sum: no stdin")?.write_all(b).map_err(|e| format!("sha256sum: {e}"))?;
    let out = child.wait_with_output().map_err(|e| format!("sha256sum: {e}"))?;
    if !out.status.success() {
        return Err("sha256sum failed on stdin".into());
    }
    let s = String::from_utf8_lossy(&out.stdout);
    let h = s.split_whitespace().next().unwrap_or("");
    if h.len() != 64 || !h.bytes().all(|c| c.is_ascii_hexdigit()) {
        return Err(format!("unexpected sha256sum output: {s}"));
    }
    Ok(h.to_string())
}

/// Runs a command, returning (success, stdout, stderr).
pub fn run(cmd: &mut Command) -> Result<(bool, String, String), String> {
    let out = cmd.output().map_err(|e| format!("{cmd:?}: {e}"))?;
    Ok((
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sha256_bytes_matches_known_digests() {
        assert_eq!(sha256_bytes(b"").unwrap(), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
        assert_eq!(sha256_bytes(b"abc").unwrap(), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    }
}

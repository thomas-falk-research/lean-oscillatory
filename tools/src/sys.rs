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

/// Runs a command, returning (success, stdout, stderr).
pub fn run(cmd: &mut Command) -> Result<(bool, String, String), String> {
    let out = cmd.output().map_err(|e| format!("{cmd:?}: {e}"))?;
    Ok((
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

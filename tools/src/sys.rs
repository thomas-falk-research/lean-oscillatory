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

/// The attribution block that may follow the frozen bytes of a file under `OscInt/Statements/` (owner decision
/// 2026-11-19, `docs/decisions/2026-11-19-attribution-blocks.md`). A statement file is its frozen bytes, or its
/// frozen bytes followed by exactly one of these blocks and nothing after it. The same two constants are in
/// `tools/oscint_check.py`; `tools/test_oscint_check.sh` and the unit test below keep them from drifting apart.
// REUSE-IgnoreStart
pub const ATTRIBUTION_BLOCKS: [&str; 2] = [
    "\n/- Attribution, appended after the freeze; not part of the frozen text (stamps/pins.txt).\nSPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>\nSPDX-License-Identifier: Apache-2.0 -/\n",
    "\n/- Attribution, appended after the freeze; not part of the frozen text (stamps/pins.txt).\nSPDX-FileCopyrightText: 2025 Joris Roos\nSPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>\nSPDX-License-Identifier: Apache-2.0\nStatement forms and constants follow roos-j/lean-oscillatory; modified 2026 by Thomas Falk III. -/\n",
];
// REUSE-IgnoreEnd

/// The bytes of `b` without one trailing attribution block, if it ends with one.
pub fn strip_attribution(b: &[u8]) -> &[u8] {
    for blk in ATTRIBUTION_BLOCKS {
        if b.ends_with(blk.as_bytes()) {
            return &b[..b.len() - blk.len()];
        }
    }
    b
}

/// SHA-256 of the frozen content of a statement file: its bytes without one trailing attribution block. A file
/// with anything after the block, or with a block that differs in one byte, is hashed whole and so matches no pin.
pub fn frozen_sha256_file(p: &Path) -> Result<String, String> {
    let b = std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?;
    sha256_bytes(strip_attribution(&b))
}

#[cfg(test)]
mod attribution_tests {
    use super::*;
    #[test]
    fn strip() {
        let frozen = b"def X : Prop := True\n";
        for blk in ATTRIBUTION_BLOCKS {
            let mut f = frozen.to_vec();
            f.extend_from_slice(blk.as_bytes());
            assert_eq!(strip_attribution(&f), frozen);
            // one block only: a second copy leaves the first in place
            let mut two = f.clone();
            two.extend_from_slice(blk.as_bytes());
            assert_eq!(strip_attribution(&two), &f[..]);
            // anything after the block, or a changed byte in it: nothing is stripped
            let mut after = f.clone();
            after.extend_from_slice(b"axiom bad : False\n");
            assert_eq!(strip_attribution(&after), &after[..]);
            let mut changed = f.clone();
            let n = changed.len();
            changed[n - 10] ^= 1;
            assert_eq!(strip_attribution(&changed), &changed[..]);
            // the block is one closed Lean comment: it starts with a newline and "/-", ends with "-/" and a newline,
            // and has no other comment delimiter inside
            assert!(blk.starts_with("\n/- ") && blk.ends_with(" -/\n"));
            let inner = &blk[3..blk.len() - 3];
            assert!(!inner.contains("-/") && !inner.contains("/-"));
        }
        assert_eq!(strip_attribution(frozen), frozen);
    }

    /// The downstream checker carries its own copy of the two constants; they must be the same bytes.
    #[test]
    fn python_copy_agrees() {
        let py = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/oscint_check.py")).unwrap();
        let body = py.split("ATTRIBUTION_BLOCKS = (").nth(1).unwrap().split("\n)\n").next().unwrap();
        let mut blocks = vec![String::new()];
        for l in body.lines().map(str::trim).filter(|l| l.starts_with("b\"")) {
            let ends_block = l.ends_with("\",");
            let lit = l.trim_end_matches(',');
            blocks.last_mut().unwrap().push_str(&lit[2..lit.len() - 1].replace("\\n", "\n"));
            if ends_block {
                blocks.push(String::new());
            }
        }
        blocks.pop();
        assert_eq!(blocks, ATTRIBUTION_BLOCKS.to_vec());
    }
}

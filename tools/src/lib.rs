// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
//! Shared code for the OscInt tool binaries: a JSON reader, the `leanexport` NDJSON reader, the canonical
//! commitment serialiser (format: `docs/commitment-format.md`), a Lean lexical scanner, and process helpers.

pub mod canon;
pub mod export;
pub mod json;
pub mod lexer;
pub mod sys;

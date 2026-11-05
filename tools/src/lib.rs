#![forbid(unsafe_code)]
//! Shared code for the OscInt tool binaries: a JSON reader, the `leanexport` NDJSON reader, the canonical
//! commitment serialiser (format: `docs/commitment-format.md`), a Lean lexical scanner, and process helpers.

pub mod canon;
pub mod export;
pub mod json;
pub mod lexer;
pub mod sys;

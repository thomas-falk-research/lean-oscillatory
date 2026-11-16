//! `oscint-cert`: an independent checker for OscInt certificates
//! (certificate contract 0.1), written from the contract alone.
//!
//! All arithmetic is exact: big integers, big rationals, and intervals with
//! dyadic rational end points rounded outward. There is no floating point
//! in the checking path and no `unsafe` code.

#![forbid(unsafe_code)]

pub mod bessel;
pub mod check;
pub mod json;
pub mod num;
pub mod quant;
pub mod sha256;
pub mod trig;

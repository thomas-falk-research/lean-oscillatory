// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Reader for the `leanexport` NDJSON stream (format 3.1.0 as emitted by Lean v4.35.0).

use crate::json::{self, Json};
use std::collections::HashMap;
use std::io::BufRead;

#[derive(Debug, Clone)]
pub enum NameC {
    Anon,
    Str(u32, String),
    Num(u32, u64),
}

#[derive(Debug, Clone)]
pub enum Level {
    Zero,
    Succ(u32),
    Max(u32, u32),
    IMax(u32, u32),
    Param(u32),
}

#[derive(Debug, Clone)]
pub enum Expr {
    BVar(u64),
    Sort(u32),
    Const(u32, Vec<u32>),
    App(u32, u32),
    Lam(String, u32, u32, u32),
    Pi(String, u32, u32, u32),
    Let(u32, u32, u32, u32, bool),
    NatLit(String),
    StrLit(String),
    MData(u32),
    Proj(u32, u64, u32),
}

#[derive(Debug, Clone)]
pub enum Kind {
    Axiom { unsafe_: bool },
    Thm,
    Def { value: u32, safety: String },
    Opaque { value: u32, unsafe_: bool },
    Quot { kind: String },
    Induct { nparams: u64, nindices: u64, all: Vec<u32>, ctors: Vec<u32>, rec: bool, unsafe_: bool, reflexive: bool, nnested: u64 },
    Ctor { induct: u32, cidx: u64, nparams: u64, nfields: u64, unsafe_: bool },
    Rec { all: Vec<u32>, nparams: u64, nindices: u64, nmotives: u64, nminors: u64, k: bool, unsafe_: bool },
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub name: u32,
    pub lparams: Vec<u32>,
    pub ty: u32,
    pub kind: Kind,
}

#[derive(Default)]
pub struct Export {
    pub names: Vec<NameC>,
    pub levels: Vec<Level>,
    pub exprs: Vec<Expr>,
    pub decls: Vec<Decl>,
    pub by_name: HashMap<String, usize>,
}

fn fld<'a>(o: &'a Json, k: &str) -> Result<&'a Json, String> {
    o.get(k).ok_or_else(|| format!("missing field '{k}'"))
}
fn u(o: &Json, k: &str) -> Result<u64, String> {
    fld(o, k)?.as_u64().ok_or_else(|| format!("field '{k}' not a natural number"))
}
fn id(o: &Json, k: &str) -> Result<u32, String> {
    u32::try_from(u(o, k)?).map_err(|e| e.to_string())
}
fn b(o: &Json, k: &str) -> Result<bool, String> {
    fld(o, k)?.as_bool().ok_or_else(|| format!("field '{k}' not a bool"))
}
fn s(o: &Json, k: &str) -> Result<String, String> {
    Ok(fld(o, k)?.as_str().ok_or_else(|| format!("field '{k}' not a string"))?.to_string())
}
fn ids(o: &Json, k: &str) -> Result<Vec<u32>, String> {
    fld(o, k)?
        .as_arr()
        .ok_or_else(|| format!("field '{k}' not an array"))?
        .iter()
        .map(|x| x.as_u64().and_then(|v| u32::try_from(v).ok()).ok_or_else(|| format!("bad id in '{k}'")))
        .collect()
}

fn put<T>(v: &mut Vec<T>, i: u64, x: T, what: &str) -> Result<(), String> {
    if i as usize != v.len() {
        return Err(format!("{what} id {i} out of order (expected {})", v.len()));
    }
    v.push(x);
    Ok(())
}

impl Export {
    pub fn read(r: impl BufRead) -> Result<Export, String> {
        let mut ex = Export { names: vec![NameC::Anon], levels: vec![Level::Zero], ..Default::default() };
        for (ln, line) in r.lines().enumerate() {
            let line = line.map_err(|e| e.to_string())?;
            if line.trim().is_empty() {
                continue;
            }
            let o = json::parse(&line).map_err(|e| format!("line {}: {e}", ln + 1))?;
            ex.record(&o).map_err(|e| format!("line {}: {e}", ln + 1))?;
        }
        for (i, d) in ex.decls.iter().enumerate() {
            ex.by_name.insert(ex.name_str(d.name), i);
        }
        Ok(ex)
    }

    fn record(&mut self, o: &Json) -> Result<(), String> {
        if o.get("meta").is_some() {
            return Ok(());
        }
        if let Some(i) = o.get("in").and_then(Json::as_u64) {
            let n = if let Some(x) = o.get("str") {
                NameC::Str(id(x, "pre")?, s(x, "str")?)
            } else if let Some(x) = o.get("num") {
                NameC::Num(id(x, "pre")?, u(x, "i")?)
            } else {
                return Err("unknown name record".into());
            };
            return put(&mut self.names, i, n, "name");
        }
        if let Some(i) = o.get("il").and_then(Json::as_u64) {
            let l = if let Some(x) = o.get("succ") {
                Level::Succ(x.as_u64().ok_or("bad succ")? as u32)
            } else if let Some(x) = o.get("max") {
                let a = x.as_arr().ok_or("bad max")?;
                Level::Max(a[0].as_u64().ok_or("bad max")? as u32, a[1].as_u64().ok_or("bad max")? as u32)
            } else if let Some(x) = o.get("imax") {
                let a = x.as_arr().ok_or("bad imax")?;
                Level::IMax(a[0].as_u64().ok_or("bad imax")? as u32, a[1].as_u64().ok_or("bad imax")? as u32)
            } else if let Some(x) = o.get("param") {
                Level::Param(x.as_u64().ok_or("bad param")? as u32)
            } else {
                return Err("unknown level record".into());
            };
            return put(&mut self.levels, i, l, "level");
        }
        if let Some(i) = o.get("ie").and_then(Json::as_u64) {
            let e = if let Some(x) = o.get("bvar") {
                Expr::BVar(x.as_u64().ok_or("bad bvar")?)
            } else if let Some(x) = o.get("sort") {
                Expr::Sort(x.as_u64().ok_or("bad sort")? as u32)
            } else if let Some(x) = o.get("const") {
                Expr::Const(id(x, "name")?, ids(x, "us")?)
            } else if let Some(x) = o.get("app") {
                Expr::App(id(x, "fn")?, id(x, "arg")?)
            } else if let Some(x) = o.get("lam") {
                Expr::Lam(s(x, "binderInfo")?, id(x, "name")?, id(x, "type")?, id(x, "body")?)
            } else if let Some(x) = o.get("forallE") {
                Expr::Pi(s(x, "binderInfo")?, id(x, "name")?, id(x, "type")?, id(x, "body")?)
            } else if let Some(x) = o.get("letE") {
                Expr::Let(id(x, "name")?, id(x, "type")?, id(x, "value")?, id(x, "body")?, b(x, "nondep")?)
            } else if let Some(x) = o.get("natVal") {
                Expr::NatLit(x.as_str().ok_or("bad natVal")?.to_string())
            } else if let Some(x) = o.get("strVal") {
                Expr::StrLit(x.as_str().ok_or("bad strVal")?.to_string())
            } else if let Some(x) = o.get("mdata") {
                Expr::MData(id(x, "expr")?)
            } else if let Some(x) = o.get("proj") {
                Expr::Proj(id(x, "typeName")?, u(x, "idx")?, id(x, "struct")?)
            } else {
                return Err("unknown expression record".into());
            };
            return put(&mut self.exprs, i, e, "expression");
        }
        let decl = |x: &Json, kind: Kind| -> Result<Decl, String> {
            Ok(Decl { name: id(x, "name")?, lparams: ids(x, "levelParams")?, ty: id(x, "type")?, kind })
        };
        if let Some(x) = o.get("axiom") {
            let d = decl(x, Kind::Axiom { unsafe_: b(x, "isUnsafe")? })?;
            self.decls.push(d);
        } else if let Some(x) = o.get("thm") {
            let d = decl(x, Kind::Thm)?;
            self.decls.push(d);
        } else if let Some(x) = o.get("def") {
            let d = decl(x, Kind::Def { value: id(x, "value")?, safety: s(x, "safety")? })?;
            self.decls.push(d);
        } else if let Some(x) = o.get("opaque") {
            let d = decl(x, Kind::Opaque { value: id(x, "value")?, unsafe_: b(x, "isUnsafe")? })?;
            self.decls.push(d);
        } else if let Some(x) = o.get("quot") {
            let d = decl(x, Kind::Quot { kind: s(x, "kind")? })?;
            self.decls.push(d);
        } else if let Some(x) = o.get("inductive") {
            for t in fld(x, "types")?.as_arr().ok_or("bad types")? {
                let k = Kind::Induct {
                    nparams: u(t, "numParams")?,
                    nindices: u(t, "numIndices")?,
                    all: ids(t, "all")?,
                    ctors: ids(t, "ctors")?,
                    rec: b(t, "isRec")?,
                    unsafe_: b(t, "isUnsafe")?,
                    reflexive: b(t, "isReflexive")?,
                    nnested: u(t, "numNested")?,
                };
                let d = decl(t, k)?;
                self.decls.push(d);
            }
            for c in fld(x, "ctors")?.as_arr().ok_or("bad ctors")? {
                let k = Kind::Ctor {
                    induct: id(c, "induct")?,
                    cidx: u(c, "cidx")?,
                    nparams: u(c, "numParams")?,
                    nfields: u(c, "numFields")?,
                    unsafe_: b(c, "isUnsafe")?,
                };
                let d = decl(c, k)?;
                self.decls.push(d);
            }
            for r in fld(x, "recs")?.as_arr().ok_or("bad recs")? {
                let k = Kind::Rec {
                    all: ids(r, "all")?,
                    nparams: u(r, "numParams")?,
                    nindices: u(r, "numIndices")?,
                    nmotives: u(r, "numMotives")?,
                    nminors: u(r, "numMinors")?,
                    k: b(r, "k")?,
                    unsafe_: b(r, "isUnsafe")?,
                };
                let d = decl(r, k)?;
                self.decls.push(d);
            }
        } else {
            return Err("unknown record".into());
        }
        Ok(())
    }

    /// Dotted display form (for lookup by the names Lean prints; escaping is not needed for our names).
    pub fn name_str(&self, n: u32) -> String {
        match &self.names[n as usize] {
            NameC::Anon => String::new(),
            NameC::Str(p, s) => {
                let pre = self.name_str(*p);
                if pre.is_empty() { s.clone() } else { format!("{pre}.{s}") }
            }
            NameC::Num(p, i) => {
                let pre = self.name_str(*p);
                if pre.is_empty() { i.to_string() } else { format!("{pre}.{i}") }
            }
        }
    }

    /// Canonical self-delimiting encoding used by the commitment format.
    pub fn name_tok(&self, n: u32) -> String {
        let mut parts = Vec::new();
        let mut cur = n;
        loop {
            match &self.names[cur as usize] {
                NameC::Anon => break,
                NameC::Str(p, s) => {
                    parts.push(format!("s{}:{}", s.len(), s));
                    cur = *p;
                }
                NameC::Num(p, i) => {
                    parts.push(format!("n{i}."));
                    cur = *p;
                }
            }
        }
        parts.reverse();
        format!("N{};", parts.concat())
    }
}

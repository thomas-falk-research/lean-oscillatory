// SPDX-FileCopyrightText: 2026 Thomas Falk III <research@thomas-falk-research.com>
//
// SPDX-License-Identifier: Apache-2.0

//! Export-side producer of statement commitments. Mirrors `tools/lean/CommitEnv.lean` line for line;
//! the format is specified in `docs/commitment-format.md`.

use crate::export::{Decl, Export, Expr, Kind, Level};
use std::collections::{BTreeSet, HashMap, HashSet};

fn bit(x: bool) -> u8 {
    x as u8
}

struct St<'a> {
    ex: &'a Export,
    lines: Vec<String>,
    lvl_ids: HashMap<String, usize>,
    expr_ids: HashMap<String, usize>,
    lvl_memo: HashMap<u32, usize>,
    expr_memo: HashMap<u32, usize>,
    refs: BTreeSet<u32>,
}

impl<'a> St<'a> {
    fn new(ex: &'a Export) -> Self {
        St {
            ex,
            lines: Vec::new(),
            lvl_ids: HashMap::new(),
            expr_ids: HashMap::new(),
            lvl_memo: HashMap::new(),
            expr_memo: HashMap::new(),
            refs: BTreeSet::new(),
        }
    }

    fn intern(&mut self, is_lvl: bool, body: String) -> usize {
        let tbl = if is_lvl { &mut self.lvl_ids } else { &mut self.expr_ids };
        if let Some(&i) = tbl.get(&body) {
            return i;
        }
        let i = tbl.len();
        let tag = if is_lvl { "L" } else { "E" };
        self.lines.push(format!("{tag}{i} {body}"));
        tbl.insert(body, i);
        i
    }

    fn lvl(&mut self, l: u32) -> usize {
        if let Some(&i) = self.lvl_memo.get(&l) {
            return i;
        }
        let body = match self.ex.levels[l as usize].clone() {
            Level::Zero => "z".to_string(),
            Level::Succ(a) => format!("s {}", self.lvl(a)),
            Level::Max(a, b) => {
                let i = self.lvl(a);
                let j = self.lvl(b);
                format!("m {i} {j}")
            }
            Level::IMax(a, b) => {
                let i = self.lvl(a);
                let j = self.lvl(b);
                format!("i {i} {j}")
            }
            Level::Param(n) => format!("p {}", self.ex.name_tok(n)),
        };
        let i = self.intern(true, body);
        self.lvl_memo.insert(l, i);
        i
    }

    fn expr(&mut self, e: u32) -> Result<usize, String> {
        if let Some(&i) = self.expr_memo.get(&e) {
            return Ok(i);
        }
        let body = match self.ex.exprs.get(e as usize).ok_or("dangling expression id")?.clone() {
            Expr::BVar(k) => format!("b {k}"),
            Expr::Sort(u) => format!("S {}", self.lvl(u)),
            Expr::Const(n, us) => {
                self.refs.insert(n);
                let ids: Vec<usize> = us.iter().map(|&u| self.lvl(u)).collect();
                let mut s = format!("c {} {}", self.ex.name_tok(n), ids.len());
                for i in ids {
                    s.push_str(&format!(" {i}"));
                }
                s
            }
            Expr::App(f, a) => {
                let i = self.expr(f)?;
                let j = self.expr(a)?;
                format!("a {i} {j}")
            }
            Expr::Lam(_, _, t, b) => {
                let i = self.expr(t)?;
                let j = self.expr(b)?;
                format!("l {i} {j}")
            }
            Expr::Pi(_, _, t, b) => {
                let i = self.expr(t)?;
                let j = self.expr(b)?;
                format!("f {i} {j}")
            }
            Expr::Let(_, t, v, b, _) => {
                let i = self.expr(t)?;
                let j = self.expr(v)?;
                let k = self.expr(b)?;
                format!("t {i} {j} {k}")
            }
            Expr::NatLit(v) => format!("n {v}"),
            Expr::StrLit(v) => format!("r {}:{v}", v.len()),
            Expr::MData(x) => {
                let i = self.expr(x)?;
                self.expr_memo.insert(e, i);
                return Ok(i);
            }
            Expr::Proj(tn, idx, s) => {
                self.refs.insert(tn);
                let i = self.expr(s)?;
                format!("j {} {idx} {i}", self.ex.name_tok(tn))
            }
        };
        let i = self.intern(false, body);
        self.expr_memo.insert(e, i);
        Ok(i)
    }

    fn names(&mut self, ns: &[u32]) -> String {
        let mut s = ns.len().to_string();
        for &n in ns {
            self.refs.insert(n);
            s.push_str(&format!(" {}", self.ex.name_tok(n)));
        }
        s
    }

    fn decl(&mut self, d: &Decl) -> Result<String, String> {
        let mut lps = d.lparams.len().to_string();
        for &n in &d.lparams {
            lps.push_str(&format!(" {}", self.ex.name_tok(n)));
        }
        let hd = format!("{} {lps} T {}", self.ex.name_tok(d.name), self.expr(d.ty)?);
        Ok(match &d.kind {
            Kind::Axiom { unsafe_ } => format!("D axiom {hd} {}", bit(*unsafe_)),
            Kind::Thm => format!("D thm {hd}"),
            Kind::Def { value, safety } => {
                if !matches!(safety.as_str(), "safe" | "unsafe" | "partial") {
                    return Err(format!("unknown safety {safety}"));
                }
                format!("D def {hd} V {} {safety}", self.expr(*value)?)
            }
            Kind::Opaque { value, unsafe_ } => format!("D opaque {hd} V {} {}", self.expr(*value)?, bit(*unsafe_)),
            Kind::Quot { kind } => format!("D quot {hd} {kind}"),
            Kind::Induct { nparams, nindices, all, ctors, rec, unsafe_, reflexive, nnested } => {
                let a = self.names(all);
                let c = self.names(ctors);
                format!(
                    "D induct {hd} {nparams} {nindices} A {a} C {c} {} {} {} {nnested}",
                    bit(*rec),
                    bit(*unsafe_),
                    bit(*reflexive)
                )
            }
            Kind::Ctor { induct, cidx, nparams, nfields, unsafe_ } => {
                self.refs.insert(*induct);
                format!("D ctor {hd} {} {cidx} {nparams} {nfields} {}", self.ex.name_tok(*induct), bit(*unsafe_))
            }
            Kind::Rec { all, nparams, nindices, nmotives, nminors, k, unsafe_ } => {
                let a = self.names(all);
                format!(
                    "D rec {hd} A {a} {nparams} {nindices} {nmotives} {nminors} {} {}",
                    bit(*k),
                    bit(*unsafe_)
                )
            }
        })
    }
}

fn lookup<'a>(ex: &'a Export, tok_of: &HashMap<String, usize>, tok: &str) -> Result<&'a Decl, String> {
    tok_of.get(tok).map(|&i| &ex.decls[i]).ok_or_else(|| format!("constant {tok} not in export"))
}

/// The commitment text for `root` (a dotted name as Lean prints it).
pub fn commitment(ex: &Export, root: &str) -> Result<String, String> {
    let &ri = ex.by_name.get(root).ok_or_else(|| format!("{root} not in export"))?;
    let tok_of: HashMap<String, usize> =
        ex.decls.iter().enumerate().map(|(i, d)| (ex.name_tok(d.name), i)).collect();
    let root_tok = ex.name_tok(ex.decls[ri].name);
    let mut seen: HashSet<String> = HashSet::new();
    let mut todo = vec![root_tok.clone()];
    while let Some(t) = todo.pop() {
        if !seen.insert(t.clone()) {
            continue;
        }
        let d = lookup(ex, &tok_of, &t)?;
        let mut scratch = St::new(ex);
        scratch.decl(d)?;
        for r in scratch.refs {
            let rt = ex.name_tok(r);
            if !seen.contains(&rt) {
                todo.push(rt);
            }
        }
    }
    let mut order: Vec<String> = seen.into_iter().collect();
    order.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    let mut st = St::new(ex);
    for t in &order {
        let d = lookup(ex, &tok_of, t)?;
        let line = st.decl(d)?;
        st.lines.push(line);
        st.refs.clear();
    }
    let mut out = format!("OSCINT-COMMIT 1 {root_tok}\n");
    for l in st.lines {
        out.push_str(&l);
        out.push('\n');
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    // A hand-written export: `def S : Prop := ∀ (p : Prop), p → p` plus an unrelated theorem.
    const TOY: &str = r#"{"meta":{}}
{"in":1,"str":{"pre":0,"str":"S"}}
{"in":2,"str":{"pre":0,"str":"p"}}
{"in":3,"str":{"pre":0,"str":"T"}}
{"ie":0,"sort":0}
{"ie":1,"bvar":0}
{"ie":2,"bvar":1}
{"ie":3,"forallE":{"binderInfo":"default","body":2,"name":0,"type":1}}
{"ie":4,"forallE":{"binderInfo":"default","body":3,"name":2,"type":0}}
{"def":{"all":[1],"hints":{"regular":1},"levelParams":[],"name":1,"safety":"safe","type":0,"value":4}}
{"thm":{"all":[3],"levelParams":[],"name":3,"type":4,"value":0}}
"#;

    #[test]
    fn toy_commitment_is_exact() {
        let ex = Export::read(Cursor::new(TOY)).unwrap();
        let c = commitment(&ex, "S").unwrap();
        let want = "OSCINT-COMMIT 1 Ns1:S;\nL0 z\nE0 S 0\nD def Ns1:S; 0 T 0 V 3 safe\n";
        let want = want.replace("V 3", "V 4");
        // E1 b 0, E2 b 1, E3 f (body E2, type E1) ... emitted in post-order of the value.
        let lines: Vec<&str> = c.lines().collect();
        assert_eq!(lines[0], "OSCINT-COMMIT 1 Ns1:S;");
        assert_eq!(lines[1], "L0 z");
        assert_eq!(lines[2], "E0 S 0");
        assert_eq!(lines[3], "E1 b 0");
        assert_eq!(lines[4], "E2 b 1");
        assert_eq!(lines[5], "E3 f 1 2");
        assert_eq!(lines[6], "E4 f 0 3");
        assert_eq!(lines[7], "D def Ns1:S; 0 T 0 V 4 safe");
        assert_eq!(lines.len(), 8, "unrelated theorem T must not enter the closure: {want}");
    }

    #[test]
    fn binder_names_and_annotations_are_ignored_body_is_not() {
        let ex = Export::read(Cursor::new(TOY)).unwrap();
        let a = commitment(&ex, "S").unwrap();
        let ex2 = Export::read(Cursor::new(TOY.replace(r#""str":"p""#, r#""str":"q""#))).unwrap();
        assert_eq!(a, commitment(&ex2, "S").unwrap());
        let ex3 = Export::read(Cursor::new(TOY.replacen(r#""default""#, r#""implicit""#, 1))).unwrap();
        assert_eq!(a, commitment(&ex3, "S").unwrap());
        let ex4 = Export::read(Cursor::new(TOY.replace(r#"{"ie":2,"bvar":1}"#, r#"{"ie":2,"bvar":0}"#))).unwrap();
        assert_ne!(a, commitment(&ex4, "S").unwrap());
    }

    #[test]
    fn missing_reference_is_an_error() {
        let bad = TOY.replace(r#"{"ie":1,"bvar":0}"#, r#"{"ie":1,"const":{"name":3,"us":[]}}"#)
            .replace(r#"{"thm":{"all":[3],"levelParams":[],"name":3,"type":4,"value":0}}"#, "");
        let ex = Export::read(Cursor::new(bad)).unwrap();
        assert!(commitment(&ex, "S").is_err());
    }
}

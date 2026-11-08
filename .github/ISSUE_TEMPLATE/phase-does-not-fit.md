---
name: My phase doesn't fit a statement
about: An oscillatory integral you need a bound for, which no OscInt statement covers (or you cannot discharge its hypotheses)
title: "Phase not covered: <short description>"
labels: ["phase-request"]
---

**The integral.** Write it out: the phase Ψ (a formula), the amplitude's support K (and whether the amplitude is
smooth with compact support), the linear terms L you need (a compact set, or all of them), the parameter set if the
phase is a family.

**Where Ψ is smooth.** An open set U ⊇ K on which you can prove `ContDiffOn ℝ 4 Ψ U` (or say why you cannot).

**The critical points.** What you know about the points of K: non-critical, nondegenerate, fold, D4 — and any other
type (cusp A₃, D₅, a degenerate curve, …). Numerical evidence is welcome; say how it was obtained.

**The bound you need.** Rate (m^{-σ}), uniformity (over L, over parameters), and whether you need constants or a
leading term.

**What you tried.** Which OscInt theorem you expected to apply (`docs/which-theorem.md`) and the hypothesis that
fails or that you cannot discharge in Lean (paste the goal).

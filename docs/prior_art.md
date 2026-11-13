# Prior art (gate run 2026-11-05)

Searched by a fresh-context search agent (sources it read are marked A) and spot-checked by the lead (L: file
downloaded and read in this session). Nothing listed was built by us. "Not found" means PLAUSIBLE-not-novel: the
search can miss work, notably Lean Zulip threads (the archive was not searchable from this session) and private
repositories.

## Verdicts

| Target | Verdict | Basis |
|---|---|---|
| S1 1D van der Corput, constants 3, 8, 18, amplitude | **ANTICIPATED** (not merged in Mathlib) | roos-j/lean-oscillatory, Mathlib PR #39406 |
| S1.k k-th derivative van der Corput, k ≥ 2, constant 5·2^{k−1} − 2, amplitude (batch A3, frozen 2026-11-09, proved in Lean at 93a8a8d; machine-checked as stated by the isolated replay of 1f7d041) | **ANTICIPATED** (not merged in Mathlib) | roos-j/lean-oscillatory `norm_integral_exp_mul_I_le_of_order_ge_two` at `cf564e0` (Sources below), under stronger regularity (`ContDiffOn ℝ k φ`, ψ `ContDiffOn ℝ 1`) than S1.k's derivative chain. Row added 2026-11-10: the external audit (`review/2026-11-10-external-audit-answers.md`) pointed out that this table omitted S1.k, although the source row below has listed the theorem since 2026-11-05. A proof of S1.k can claim only a machine-checked port under weaker regularity. AI-use disclosure (added 2026-11-13): the Lean proof of S1.k for every k (`OscInt/Cusp/VdCk.lean`) was drafted with an OpenAI model (the reviewer's tool; version not stated for this packet) and integrated by the lead (`review/2026-11-12-A3-packet-answers.md`). It had no route review; it was read by the post-proof referees (`review/2026-11-12-A3-post-proof-answers.md`) |
| S5.1′ / S5.1 uniform A3 cusp bound t^{−3/4}, C² amplitudes, uniform in the linear term (batch A3, frozen 2026-11-09, proved in Lean at 93a8a8d; machine-checked as stated by the isolated replay of 1f7d041) | **AI-assisted route, disclosed** (owner decision 2026-11-10) | AI-use disclosure, following the COPE and ICMJE practice of naming the tool and version (not as authorship or credit): the complete hand proof was produced with OpenAI ChatGPT 6 (version as given by the owner), 2026-11-10. Responsibility for its use rests with the project. Checked by the lead and a fresh-context referee, and re-derived in `review/2026-11-10-external-results-answers.md`. The mechanism (exact transverse dephasing plus an order-4 van der Corput estimate) and the exponent are classical. Ikromov–Müller and Borovyk–Goldberg give C³-amplitude cusp estimates (reported by the reviewer, not re-read by the lead); C² control was not found in the reviewer's logged search. The Lean proofs of the A3 parts and of S1.k (2026-11-12) were drafted with an OpenAI model (the reviewer's tool; version not stated for this packet; corrected 2026-11-13 from "the same external tool", which the record does not support). The cusp parts follow the route refereed at b719ba4 (P4 deviates, recorded in `docs/proof-A3.md`); S1.k for general k had no route review. Compiled, fixed in five places and integrated by the lead (`review/2026-11-12-A3-packet-answers.md`); post-proof reviews answered in `review/2026-11-12-A3-post-proof-answers.md` |
| T0E′ / T6E′ cube-root bound for the 1D lattice kernel, constant 8(1 + √7)/3, all real ξ (batch LE2, frozen and reviewed 2026-11-10/11, proved in Lean at 48e7f24; see `docs/STATUS.md` for the replay) | **AI-assisted route, disclosed** (owner decision 2026-11-10) | AI-use disclosure, as for S5.1′ (tools named, not authorship or credit): the constant and the hand proof come from an external reviewer's submission produced with OpenAI ChatGPT 6 (version as given by the owner, not verified by the lead), 2026-11-10. The lead's re-derivation, the blind statement referees, the route referee, the post-proof referees and the proof agents who wrote the Lean parts are all instances of Claude (Anthropic), the lead's own tool (also named in the commit trailers); "independent" in these records means fresh-context, not a different model family or a human. "Found TRUE by two blind referees" means floating-point evidence and hand checks; the Lean proof is the machine check. Responsibility for the use of both tools rests with the project. Re-derived by the lead (`review/2026-11-10-external-followup-answers.md`, Result 1, with its 2026-11-11 correction of one unjustified step). The ingredients (integration by parts with end-point terms, arcsine band lengths, convexity) are classical; for integer ξ Landau's sharp constant 2π·0.7857 is smaller. The constant was not found in the reviewer's logged search, which the lead did not re-run; that is the entire novelty claim |
| TdF / TdE′ the d-dimensional hypercubic lattice kernel, decay t^{−d/3} with constant (8(1 + √7)/3)^d (batch HC, frozen 2026-11-12, proved in Lean at 5a5f714 and replayed; see `docs/STATUS.md`) | **ANTICIPATED** (rate and factorisation; the explicit constant is new only through T0E′) | A. Stefanov and P. G. Kevrekidis, *Asymptotic behaviour of small solutions for the discrete nonlinear Schrödinger and Klein–Gordon equations*, Nonlinearity 18 (2005) 1841–1857 (arXiv nlin/0409009): ℓ¹ → ℓ^∞ decay (1 + \|t\|)^{−d/3} for the discrete Schrödinger group on ℤ^d, non-explicit constant (CITED-ABSTRACT, read at abstract level 2026-11-12). The factorisation is Fubini. Claim: machine-checked, with an explicit constant |
| LS-E, LS-K, LS-D, LS-D′ the free lattice Schrödinger group on ℤ^d: existence, kernel representation and uniqueness, dispersive decay with explicit constants (batch LS, frozen and reviewed 2026-11-12, not proved; route `docs/proof-LS.md`) | **ANTICIPATED** (rate; the explicit constants are new only through T0E′ and TdE′) | A. Stefanov and P. G. Kevrekidis, Nonlinearity 18 (2005) 1841–1857: ℓ¹ → ℓ^∞ decay (1 + \|t\|)^{−d/3} for the discrete Schrödinger group, non-explicit constant (CITED-ABSTRACT, as in the TdF/TdE′ row). The existence and kernel identities are classical functional analysis (bounded generator, exponential series). Statements, sanity layer, route and assembly by the lead (a Claude instance); blind statement referees and the route referee also Claude instances (`review/2026-11-12-LS-pre-proof-answers.md`, `docs/proof-LS.md`). Claim: machine-checked statements with explicit constants, once proved |
| S2 2D nondegenerate stationary phase, uniform in p | PARTIAL | non-stationary O(μ^{-N}) in ℝⁿ and O(λ^{-n/2}) for *definite* Hessians, existential constants (roos-j/lean-variationalsw); no indefinite case |
| S3 uniform fold, m^{-5/6} | not found | only a 1D cubic-point limit (lean-DLMF) |
| S4 D4 umbilic, t^{-2/3}, constant Γ(1/3)²/(√3·\|Disc\|^{1/6}) (and, found here, Γ(1/3)²/Disc^{1/6} for the elliptic umbilic; PLAUSIBLE known, no novelty claimed) | not found | lean-DLMF defines umbilic canonical integrals on complex contours; their link to real integrals is `sorry` there |
| Infrastructure | PARTIAL | Mathlib: whole-space integration by parts, normed-parameter IFT, non-parametric multivariate Taylor (`docs/toolchain.md`) |

## Sources

| Item | URL | What it proves | Verdict | Read |
|---|---|---|---|---|
| roos-j/lean-oscillatory `LeanOscillatory/VanDerCorput.lean` at `cf564e0e100e91de222a53b85b106fa9a03a0ec5` (Joris Roos, Manasa Praveen; Apache-2.0 header; Lean v4.32.0-rc1) | https://github.com/roos-j/lean-oscillatory | `c k = 5·2^(k−1) − 2`. `norm_integral_exp_mul_I_le_of_order_one`: `ContDiffOn ℝ 2 φ [[a,b]]`, `L ≤ \|derivWithin φ\|`, `derivWithin φ` monotone, `0 < L`, `ψ` `ContDiffOn ℝ 1` (Banach-valued) ⇒ `‖∫ exp(φ x·I)•ψ x‖ ≤ c 1·L⁻¹·(‖ψ b‖ + \|∫‖derivWithin ψ‖\|)`. `…_order_ge_two` (k ≥ 2, `ContDiffOn ℝ k φ`, `L ≤ \|iteratedDerivWithin k φ\|`): `c k·L^(−1/k)·(…)`. 494 lines, no `sorry` | ANTICIPATES S1 | L, A |
| Mathlib PR #39406 "van der Corput's lemma" (same authors), open, `awaiting-author` | https://github.com/leanprover-community/mathlib4/pull/39406 | the file above as `Mathlib/Analysis/OscillatoryIntegrals/VanDerCorput.lean` | ANTICIPATES S1 | A |
| roos-j/lean-dfr `DFR/Auto/VanDerCorput.lean` | https://github.com/roos-j/lean-dfr | first derivative 4/μ (no amplitude); k ≥ 2 with existential constant | PARTIAL S1 | A |
| fxeqxmulfx/transformer `Section5_*DerivativeTest` | https://github.com/fxeqxmulfx/transformer | first derivative 4/(\|ρ\|δ), second 10/√(\|ρ\|κ), no amplitude | PARTIAL S1 | A |
| roos-j/lean-spherical `RS/KernelEstimate.lean`, `OneDimStationaryPhase.lean` | https://github.com/roos-j/lean-spherical | second-derivative test with amplitude, (10M + 2M₁(b−a))/√(λκ); 1D quadratic stationary phase | PARTIAL S1, 1D analogue of S2 | A |
| roos-j/lean-variationalsw `OscillatoryIntegralEstimates.lean`, `CarlesonSjolin.lean` | https://github.com/roos-j/lean-variationalsw | ℝⁿ non-stationary phase ≤ C μ^{−N} Σ∫‖D^k a‖; strongly convex phase ≤ C λ^{−n/2}; 2D integration by parts for O(μ^{−4}) | PARTIAL S2, infrastructure | A |
| bjbraams/lean-DLMF `Analysis/Asymptotics/StationaryPhase.lean`, `CoalescingSaddles/*` | https://github.com/bjbraams/lean-DLMF | 1D cubic-point limit λ^{1/3}∫ → Γ(4/3)c^{−1/3}e^{iπ/6}; umbilic canonical integrals (contour definitions), scaling; real-integral representations `sorry` | PARTIAL (adjacent to S3, S4) | A |
| fpvandoorn/carleson `Classical/VanDerCorput.lean`, `HolderVanDerCorput.lean` | https://github.com/fpvandoorn/carleson | linear phase e^{inx} bound; Hölder version on doubling spaces | UNRELATED | A |
| rwst/lean-code, TomasOrtega/Sidon, roos-j/lean-discretesw | (see agent log) | van der Corput *difference inequality* for exponential sums | UNRELATED | A |
| AxiomMath/PrimeNumberTheoremAnd `IEANTN/ZetaAppendix.lean` | https://github.com/AxiomMath/PrimeNumberTheoremAnd | 1D first-derivative non-stationary bound | PARTIAL S1 | A (blueprint text only) |
| Isabelle AFP (mirror) | https://github.com/isabelle-prover/mirror-afp-devel | code search "Corput", "oscillatory", "stationary phase": nothing | not found | A |
| Rocq: MathComp-Analysis, Coquelicot | https://github.com/math-comp/analysis | "Corput", "oscillatory": nothing | not found | A |
| HOL Light, HOL4 | https://github.com/jrh13/hol-light, https://github.com/HOL-Theorem-Prover/HOL | "Corput": nothing | not found | A |
| zbMATH Open API | https://api.zbmath.org/v1/document/_search | "stationary phase & formal proof": 13 hits, all informal | not found | A |
| arXiv API | https://export.arxiv.org/api/query | "van der Corput" ∧ Lean, "stationary phase" ∧ Lean, formalization ∧ oscillatory: nothing relevant | not found | A |
| Mathlib at the pin | local clone | no van der Corput, no stationary phase (`docs/toolchain.md`) | not found | L |

Not checked directly: PFR, sphere-eversion, FLT (their repositories could not be listed from the session; none
appeared in the cross-repository code searches), Lean Zulip archive.

## Lattice kernels T6, T6L: classical, separable (disclosure added 2026-11-08, session 7)

Found by the lead while preparing session 7; neither the GD pre-proof nor the post-proof referees, nor an external
review of `main` at 96f55a2, raised it. **Severity MEDIUM (presentation; no proof is affected).**

The kernel of T6 (`latticeKernel` in `OscInt/Statements/Global.lean`) integrates over the square `[−π, π]²` and its
phase `t(cos k₁ + cos k₂) + x₁k₁ + x₂k₂` is a sum of a `k₁` part and a `k₂` part, so by Fubini
`K(t, x) = I(t, x₁) · I(t, x₂)` with `I(t, n) = ∫_{−π}^{π} e^{i(t cos k + nk)} dk = 2π iⁿ Jₙ(t)` (Bessel's integral).
PROVEN on paper (Fubini and the Bessel integral, DLMF 10.9.2); the factorisation is machine-checked by batch LE
(statement T6F; proved and replayed on a1d2a64, post-proof reviews `review/2026-11-08-LE-post-proof-{A,B}.md`), the
Bessel identification is not formalised (Mathlib has no Bessel functions at the pin).
Consequences:
- **T6** is equivalent to the classical bound `sup_n |Jₙ(t)| ≤ c t^{−1/3}`. L. J. Landau, *Monotonicity and bounds on
  Bessel functions*, Electron. J. Differ. Equ. Conf. 04 (2000) 147–154, states the best constant `c = 0.7857···` for
  `|J_ν(x)| ≤ c x^{−1/3}`, `ν ≥ 0`, `x > 0` (its inequality (10); paper read 2026-11-09 from
  https://ejde.math.txstate.edu/conf-proc/04/l1/landau.pdf; cited in Fungrim, https://fungrim.org/entry/7f3485/). That
  paper surveys, and cites as its reference [5], the full treatment: L. J. Landau, *Bessel functions: monotonicity and
  bounds*, J. London Math. Soc. (2) 61 (2000) 197–215, DOI 10.1112/S0024610799008352 (bibliographic record checked
  against Crossref 2026-11-09; that paper not read). `c = sup_{x>0} x^{1/3} J₀(x)`, attained at the first stationary
  point `x₀ ≈ 0.7837`: recomputed 2026-11-09 with mpmath at 40 digits (not rigorous) as `c = 0.785746870498513…`,
  `x₀ = 0.783662818503470…` (the paper's table gives 0.7837). In our normalisation
  `|I(t, n)| ≤ 2π c t^{−1/3} ≈ 4.937 t^{−1/3}` (an earlier version of this entry rounded c to 0.7858; 0.7857 is correct
  to four places). The registered LE protocol (`docs/prereg/2026-11-08-LE-lattice-constants.md`), its program
  (`numerics/src/bin/lattice1.rs`) and the LE reviews keep 0.7858 and are not edited (registered and verbatim
  records). No verdict depends on the rounding: criterion (c) tested `max t^{1/3}|I|/(2π) ≤ 0.7858 + 1e−4`, a threshold
  above the true c (by about 1.5e−4) with either value, and the ratios it reports change in the fourth digit.
- **T6L** is the classical Cauchy–Watson asymptotic `Jₙ(n) ~ Γ(1/3) / (2^{2/3} 3^{1/6} π) · n^{−1/3}`:
  `4π² (Γ(1/3) / (2^{2/3} 3^{1/6} π))² = Γ(1/3)² 2^{2/3} 3^{−1/3} = Γ(1/3)² 48^{1/6} / √3`, the frozen constant.
- The proof in the repository is genuine and does exercise the global theorem (the points `(±π/2, ±π/2)` are D4 points
  of the 2D phase), but T6 and T6L **are not evidence that GD reaches non-separable symbols**. That needs a
  non-separable model (session-7 batch VV: a two-band or triangular-lattice symbol).
- No novelty is claimed for the mathematics of T6, T6L; the claim is "machine-checked", nothing more.
- Scope (adversarial review m2): every GD demonstration in the repository uses a separable phase (T6; x³ + y³ in the
  consumer example). The candidate non-separable model of batch VV, the QWZ band at m = 3, turned out to have exact cusp
  points (`docs/design/vector-amplitudes.md` §6), so no proved theorem applies to it; no non-separable symbol satisfying
  the GD hypotheses has been found yet.

## Singularities of lattice dispersion relations (CENSUS prior art; added 2026-11-09)

Logged sweep: `review/2026-11-09-CENSUS-prior-art-sweep.md` (244 queries, `review/2026-11-09-CENSUS-prior-art-querylog.tsv`;
the brief is not published). Keys: [CR] record checked against Crossref, [arX] arXiv
text read, [not read] record only. Per-model classifications of every torus point for the phase `Ψ − ∇Ψ(k₀)·k`, the
problem of the census (`docs/prereg/2026-11-09-CENSUS-spec.md`), already exist for:
- the discrete Klein–Gordon equation on ℤ²: J.-C. Cuenin, I. A. Ikromov, *Sharp time decay estimates for the discrete
  Klein–Gordon equation*, Nonlinearity 34 (2021) 7938–7962, DOI 10.1088/1361-6544/ac2b86, arXiv:2011.12076 [CR][arX]
  (mass 1; 2D rate |t|^{−3/4}; A_k with k ≤ 3, A3 exactly at cos x₁ = cos x₂ = 0, Prop. 9); V. Borovyk, M. Goldberg,
  *The Klein–Gordon equation on ℤ² and the quantum harmonic lattice*, J. Math. Pures Appl. 107 (2017) 667–696,
  DOI 10.1016/j.matpur.2016.10.002, arXiv:1304.6353 [CR][arX] (all masses, anisotropic couplings; folds and cusps only);
- the lattice wave equation: P. Schultz, *The wave equation on the lattice in two and three dimensions*, Comm. Pure
  Appl. Math. 51 (1998) 663–695 [CR, not read]; C. Bi, J. Cheng, B. Hua, *The wave equation on lattices and
  oscillatory integrals*, arXiv:2312.04130 [arX];
- the triangular lattice: H. Ge, B. Hua, L. Jia, P. Zhou, Calc. Var. PDE 64 (2025) art. 176,
  DOI 10.1007/s00526-025-03026-1, arXiv:2412.02947 [CR][arX] (A2 or A3 only, Lemma 4.3; rate |t|^{−3/4});
- the King's graph (t–t′ at t′ = t): Z. Wan, H. Zhang, arXiv:2507.20142 [arX] (A1, A2, A3 only);
- graphene: Y. Hong, Y. Tadano, C. Yang, Adv. Math. 507 (2026) 111368, DOI 10.1016/j.aim.2026.111368,
  arXiv:2503.08996 [CR][arX] (degenerate set three curves; global rate 2/3; Dirac cones).
Related, not the same problem: classifications of the critical points of the band itself (∇ε = 0, higher-order van
Hove singularities): A. Chandrasekaran, A. Shtyk, J. J. Betouras, C. Chamon, Phys. Rev. Research 2 (2020) 013355,
DOI 10.1103/physrevresearch.2.013355 [CR][arX]; N. F. Q. Yuan, H. Isobe, L. Fu, Nat. Commun. 10 (2019) 5769,
DOI 10.1038/s41467-019-13670-9 [CR][arX]. Numerical schemes lose dispersion where the symbol's Hessian degenerates:
L. I. Ignat, E. Zuazua, SIAM J. Numer. Anal. 47 (2009) 1366–1390, DOI 10.1137/070683787 [CR, abstract]; no
classification of Yee/FDTD caustics was found. 2D quantum walks: K. Watabe, N. Kobayashi, M. Katori, N. Konno,
Phys. Rev. A 77 (2008) 062331, DOI 10.1103/physreva.77.062331 [CR][arX] (limit distributions; eq. (7) dispersion);
Y. Baryshnikov, W. Brady, A. Bressler, R. Pemantle, *Two-dimensional quantum random walk*, J. Stat. Phys. 142 (print
2011, online 2010) 78–107, DOI 10.1007/s10955-010-0098-2 [CR][arX] (caustic geometry); no 2D quantum-walk ℓ¹ → ℓ^∞ dispersive estimate was found. General theory: V. I. Arnol'd,
Funct. Anal. Appl. 6 (1972) 254–272, DOI 10.1007/bf01077644 [CR]; A. N. Varchenko, Funct. Anal. Appl. 10 (1976)
175–196, DOI 10.1007/bf01075524 [CR]; I. A. Ikromov, M. Kempe, D. Müller, Acta Math. 204 (2010) 151–271,
DOI 10.1007/s11511-010-0047-6 [CR]; I. A. Ikromov, D. Müller, *Fourier Restriction for Hypersurfaces in Three Dimensions
and Newton Polyhedra*, Princeton UP 2016, DOI 10.1515/9781400881246 [CR] (Crossref and zbMATH differ by a year for the
two Funct. Anal. Appl. papers; the Crossref year is given). Formalisations: none of 2D degenerate (A2/A3/D4) bounds or
of singularity classification was found in Mathlib, Isabelle AFP or Coq (code search; 1D Morse stationary phase exists
in roos-j/lean-spherical).

**What follows.** No census across several models was found, nor a classification for the t–t′ model at general t′/t,
the 9-point stencil, Yee/FDTD, Qi–Wu–Zhang, gapped graphene or 2D quantum walks: PLAUSIBLE-not-novel (search limits:
Google Scholar unreachable, Crossref search largely rate-limited, several texts paywalled). For the models above, the
census re-derives published results and claims no novelty; they serve as external known answers (spec §5). A machine-checked
A3 (cusp) bound would serve the largest set of already-classified models (discrete Klein–Gordon, triangular lattice,
King's graph, lattice wave equation).

## Consequence

S1 must cite roos-j/lean-oscillatory and PR #39406. Building it again from scratch would duplicate open
upstream work; the decision how to proceed with M1 is the owner's (see `docs/HANDOFF.md`).

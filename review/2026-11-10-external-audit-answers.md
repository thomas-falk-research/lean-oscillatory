# Answers to the external research audit of 2026-11-10

Subject: an external reviewer's research audit and strategy memorandum of 2026-11-10, with one SymPy script. They are
not recorded (owner privacy rule, lessons 46); section labels (§2, memo §3, …) refer to them, and each claim is stated
below in the lead's words. Written by the session-9 lead. Each claim is sorted into the bins agreed with the
owner: already present / correct but classical or out of scope / candidate / wrong. Candidates go to ROADMAP
"Candidates" only, and are promoted through its four gates.

**Evidence.**
- The audit's script was run unchanged, from an empty directory with `python3 -I`: `EXACT CHECKS PASS`. Its SHA-256 matched the
  value the memo states.
- `numerics/review/audit_checks.py` adds four exact checks of what the example implies for I3b, all passing; record
  `numerics/results-audit-checks-2026-11-10.txt`.
- A web check of the four external sources the memo cites (summarised in the last section). Pages that loaded only in
  part are marked as such.

## Verdict

The audit is careful, and much more measured than its title. Its own conclusion says it established no new theorem,
no solver and no physics breakthrough. Two items change the repository: the dimension-lift obstruction, and the S1.k
disclosure gap. Three become candidates. One methodological point needs an owner decision. The decade programme
itself re-describes the existing roadmap in longer time units: each of its five proposed first research questions
maps onto an item that already exists.

## Items that change the repository

1. **§2 / memo §3, dimension-lift obstruction: CORRECT. It is a precision fix to I3b, and it does not refute I3b as intended.**
   - The phase `Φ = (z + x)²/2 + (x − 1/2)(x + 3y²)²` has all the properties the audit states.
   - The lead's checks add what it implies:
     - the full Hessian at 0 is `[[0,0,1],[0,0,0],[1,0,1]]`, of rank 2, so the point has corank 1 and is not a
       corank-2 (D4-type) point of the 3D phase at all (A1);
     - eliminating `z` gives `(x − 1/2)(x + 3y²)²`, with a rank-1 Hessian and the critical curve `x = −3y²` (A2).
   - The correct hypothesis is intrinsic: corank exactly 2, plus a nondegenerate cubic `D³Φ(0)` on `ker D²Φ(0)`. It
     agrees with "the reduced phase is D4", because elimination changes only terms of order ≥ 4 (A4). It accepts the
     coupled positive control `(z + xy)²/2 + x³ − 3xy² + zx²` and rejects the audit's phase (A3).
   - The `t^{−1}` rate along the critical curve is classical (Morse–Bott, codimension 2) and was not checked here.
   - ROADMAP I3b's wording ("a D4 point in two variables, coupled to d − 2 nondegenerate directions") allowed the
     wrong reading, so it now states the intrinsic hypothesis, names the audit's phase as a required bite datum, and
     names the positive control. Same mechanism as the dossier's N2 (raw versus reduced quartic): restriction is not
     reduction.
2. **Memo §2 and §7, S1.k overlaps Roos–Praveen: CORRECT. A disclosure gap, now fixed.**
   - `docs/prior_art.md` has listed `roos-j/lean-oscillatory`'s `norm_integral_exp_mul_I_le_of_order_ge_two` (k ≥ 2,
     constant `5·2^{k−1} − 2`) in its Sources table since 2026-11-05.
   - But its verdict table did not list S1.k when batch A3 was frozen, and `docs/statements.md` cites Roos–Praveen
     only for the forms and constants.
   - The verdict table now marks S1.k ANTICIPATED, under stronger regularity (`ContDiffOn ℝ k φ`, ψ `ContDiffOn ℝ 1`)
     than S1.k's derivative chain. A proof of S1.k can claim only a machine-checked port under weaker regularity.
   - The obvious route is to port that proof; `docs/HANDOFF.md` records it.
   - The upstream state was confirmed on 2026-11-10: Mathlib PR #39406 is open, labelled `awaiting-author`, and lists
     the order ≥ 2 theorem.
3. **Memo §7, our roadmap overstated Ikromov–Müller: PLAUSIBLE, and our wording is weakened.**
   - ROADMAP I3 said their height bound "covers all finite-type 2D singularities".
   - The audit reports an exception involving an unbounded principal Newton face. Neither the audit's claim nor ours
     has been checked against the paper (CITED-UNREAD).
   - I3 now says "broad classes … exact hypotheses not yet read".

## Candidates (added to ROADMAP "Candidates", not to the roadmap)

- **Finite-type fallback, `t^{−1/N}` uniform in the linear term, any dimension (§3, memo §4).**
  - Classical (Stein 1993, Ch. VIII §2, cited from memory). The audit says so.
  - In OscInt terms it is S1.k plus Fubini plus a partition of unity, so it comes nearly free once S1.k is proved.
  - Its value would be a weak but universal baseline for CENSUS models outside the A2/A3/D4 catalogue. Whether that
    matters is what I1 decides (gate 1).
  - The prior art to compare first is Greenblatt, "Oscillatory integrals and weighted gradient flows", Rev. Mat.
    Iberoam. 41 (2025) 1583–1598, DOI 10.4171/RMI/1529. Its abstract was read and does mention estimates uniform
    under linear perturbations; the paper was not read.
- **Newton-polyhedron bounds on top of the formalized Hironaka resolution (§4, memo §7).**
  - The formalization exists: resolutionorg/hironaka v1.0.0, announced 2026-10-06. It covers characteristic 0,
    algebraic schemes, and real- and complex-analytic spaces, and the project says it uses no `sorry` and only the
    three standard axioms. The lead has not verified that, nor its Lean toolchain.
  - The audit is right that existence of a resolution is not an effective bound. In 2D the explicit Newton-polygon
    route of Ikromov–Müller and Greenblatt is the more direct one.
  - Waits on I1 selecting finite-type families beyond A3 and D4.
- **Matrix-valued propagators through gap closings (§3 table, memo §6 F).** A direction without a statement; waits on
  gates 1 and 2.

## Already present (no change)

- **§1 status.** Accurate as of 0f1411d. The branch has since moved on with the CENSUS control, I7 and the candidate
  gates.
- **§5 gradient-map geometry.** CENSUS spec §2 already classifies every point through `φ_{k₀} = Ψ − ∇Ψ(k₀)·k`, the
  phase of the observation direction `x/t = −∇Ψ(k₀)`. The QWZ sign trap is handled in spec §7.
- **§8, the five research questions:**
  1. Q1 transverse elimination: I3a and I3b.
  2. Q2 automatic certificates: I2 and I5.
  3. Q3 parameter-uniform bounds through transitions: session-7 order item 4, "D4 bound uniform over compact
     families (read Karpushkin and Duistermaat 1974 first)", together with the audit's Karpushkin caution.
  4. Q4 usable constants: I4 and `docs/constants.md`.
  5. Q5 certified classifier: I1.
- **Memo §8, certificate architecture.** I5: the trust boundary, "only the defined checker may give CERTIFIED", and
  interfaces frozen after two cross-domain consumers. Adding UNKNOWN / OUT_OF_SCOPE outcomes fits I5 when its schema
  is written.
- **§6 efficiency table.** The points about constants are I4 and `docs/constants.md`. Its suggestions to charge each estimate only for the amplitude derivatives it uses, and to hash dependency closures
  incrementally, are reasonable engineering notes for when those files are next
  changed, not research items.
- **§5 quartic-unfolding scaling.** Classical, and the audit says so.

## Proposed for an owner decision (not applied)

- **CENSUS held-out models (memo Gate 3).**
  - The unlock ranking (spec §4.3) is computed on 18 models that the project chose. To test whether the ranking
    generalises, a small held-out set would need to be fixed before the run and used only after it.
  - Ideally a third party would choose that set, from the same five domains.
  - The CENSUS registration is still a draft, so this can be added now, as K-QWZm was. After registration it would
    have to be a separately registered follow-up.
  - Recommendation: yes, 4–6 models, frozen by hash before the first run.

## Out of scope or premature

- **The 2026–2036 timeline (§7, memo §10).** Recorded, not adopted. Its first stage, 2026–2028, is the current
  roadmap, and the later stages have no evidence yet to schedule against. The roadmap's rule (a tick needs evidence)
  and the candidate gates already enforce the audit's own acceptance criteria.
- **Gate 6, benchmarks at d = 2…100.** Premature: no d-dimensional theorem exists to benchmark. It belongs after I3b.
- **Gate 7, two consumers from different fields.** This is I5's rule already.

## External sources (web check 2026-11-10, by a fetch agent; facts only)

- **Mathlib PR #39406**, "feat(Analysis): van der Corput's lemma" (roos-j, with M. Praveen): open; labels
  `awaiting-author`, `new-contributor`, `t-analysis`; declares
  `Oscillatory.norm_integral_exp_mul_I_le_of_order_ge_two`.
- **resolutionorg/hironaka:** "Hironaka's resolution of singularities in characteristic zero, formalized in Lean 4
  over Mathlib".
  - The README claims algebraic schemes and real- and complex-analytic spaces, no `sorry`, and axioms `propext`,
    `Classical.choice` and `Quot.sound` only.
  - The blog post is dated 2026-10-06, for v1.0.0. It says the work was produced by an automated process, then audited
    and refactored by named people.
  - Toolchain not read. None of this is verified by the lead.
- **Greenblatt (2025)**, Rev. Mat. Iberoam. 41(4) 1583–1598, DOI 10.4171/RMI/1529. Abstract: "We prove a theorem which
  provides estimates that are uniform with respect to linear perturbations of the phase".
- **roos-j/lean-oscillatory:** its README lists the order ≥ 2 and order 1 theorems as completed. The file itself was
  not re-read; the lead's 2026-11-05 reading at `cf564e0` is in `docs/prior_art.md`.

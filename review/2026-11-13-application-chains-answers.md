# Answers to the external application-chains dossier, 2026-11-13

Subject: two archives from the same external reviewer as `review/2026-11-12-A3-packet-answers.md`.
- "Application chains" research dossier, written against 93a8a8d. SHA-256
  0648408b8f8fc1113b775ca2162e840c3e51f66757a11bd4a983e882482d0c03; no hash was relayed for it, and the update archive
  records the same value as its base.
- Its update after the lead's referee findings, written against e814510. SHA-256
  c6086c80344a4ccac119d3e0c961c1541ac4c1c2870223cc1ca57d718eefc910, which matches the hash the owner relayed.

The archives, the prompt and the chat are not recorded (owner privacy rule, lessons 46). Each claim is restated in the
lead's words. Written by the session-10 lead.

## What arrived

- **No Lean.** There are no new proofs, no build and no replay.
- **Hand propositions P1–P6:**
  - P1: integrals of the capped envelope min{1, (t₀/t)^α}, and an input-to-peak response gain;
  - P2: the memory kernel of an emitter coupled with opposite signs to two sites of the cosine chain;
  - P3: a finite-horizon error bound for truncating that memory;
  - P4: the same for the linearised Vlasov density equation;
  - P5: a resolvent control showing that a decay bound does not locate spectral singularities;
  - P6: a covariance obstruction for hard truncation of a thermal memory kernel, and a positive-definite taper.
- **An imaging example:** an explicit bound on omitted blocks of a scalar SAR normal operator, with a mirror-pair and a
  hard-window control.
- **Three Python suites with their outputs, and a manifest.**
- **Domain notes and source ledgers, and an audit of this repository.**
- **The packet's own framing:** it says the propositions are "derivations in this packet, not OSCINT theorems and not
  priority claims", and it makes no novelty claim.

## What the lead did

1. **Integrity.** Both hashes were computed. Every file in both manifests was checked with the lead's own code: no
   mismatch, no unlisted and no missing file.
2. **No packet script was run.** The scripts were scanned for unsafe constructs. The packet's verifier uses `subprocess`
   in its replay mode.
3. **Reading.**
   - Read in full: the report, the propositions, the claims register, the consumer targets, the review answers, the
     two update notes, the two domain notes, the repository audit and the pin addenda, and the root check script, to
     learn its parameters.
   - Scanned, not read line by line: the other scripts and the provenance ledgers.
4. **Independent checks.** `numerics/review/application_chains_checks.py`, record
   `numerics/results-application-chains-checks-2026-11-13.txt`; all PASS.
   - **P2.** M(t) = g²·2J₁(z)/z with z = 2Jt. With a phase error ε the kernel is g²[J₀(z) + cos ε·J₂(z)]. Both checked
     against high-precision quadrature, to about 10⁻³⁰. Also I(z, 1) = 2πi·J₁(z) for the repository's `latticeKernel1`.
   - **P2 envelope.** T0E′ gives |M| ≤ g² min{1, (C*/π)(2Jt)^{−4/3}}, and its integral is 4t_m.
   - **P3.** The three bounds Q/(1 − Q) match to six digits.
     - The emitter errors were reproduced to within 10⁻⁶ with the lead's own solver, against an open chain of 1,203
       sites. The packet used a ring.
     - These runs take Ω = 0.
   - **P4.**
     - The table matches.
     - The sign of the feedback kernel was checked by direct integration.
     - The two scalar controls (2eᵗ − 1, and 1/3 + (2/3)e^{−3t}) were checked by inverse Laplace transform.
   - **P5.** The two limits hold.
   - **P6.**
     - The spectral representation holds.
     - The hard-truncation Fourier value ĥ(3π/2) ≈ −0.2484 is below the stated bound −0.1221.
     - The taper tail formula holds, with T ≈ 168,745 for tolerance 0.1.
   - **Imaging.** 512/1225 and 336/(5√5) are exact (SymPy). The delay gap is at least 1; sampled on the boundary circles
     it is at least 1.26. The mirror pair has ratio 1.
5. **A fresh-context mathematics referee** (a Claude instance, 23:36:40 to 23:51:17 UTC) re-derived everything with its
   own scripts.
   - It ran no packet script and no Lean.
   - Verdict: every proposition and the imaging bound TRUE; no BLOCKER, no MAJOR.
6. **A prior-art check** (a Claude instance, 23:36:39 to 23:43:11 UTC). Sources were labelled READ, ABSTRACT-ONLY or
   NOT ACCESSED.

## Verdicts and prior art

**The mathematics: TRUE (hand proofs and floating-point checks; not machine-checked).** The referee found no BLOCKER and
no MAJOR. Its findings, which the reviewer accepted as errata:
- **MINOR.** The emitter table does not state Ω = 0. At Ω = 0.5 the errors are 0.0261, 0.0066 and 0.0016. The bounds do
  not depend on Ω.
- **MINOR.** The table measures the emitter-component error. That error is bounded by the full-state error D_H, which is
  what the bound covers.
- **NITs:**
  - D_H must be known to be finite before D_H ≤ (1 + D_H)Q is solved for D_H. It is: the truncated solution is
    continuous on [0, H].
  - The hard-truncated kernel is discontinuous, so Bochner's theorem for continuous functions does not apply as
    written. The conclusion holds: a finite Gram matrix has eigenvalue −3.86.
  - The phase-error claim needs J > 0.
  - The time scale t₀ assumes the dispersion −2J Σ cos k_j.
  - With the exact constant the imaging threshold is t ≥ 174; 179 is for the rounded constant 32.
- **One referee finding the lead does not accept.**
  - The referee said the plasma scheme converges at first order. For the packet's trapezoid scheme, with the cutoff T
    on a grid point, the successive differences shrink by a factor of 4.00 at each halving (record above), which is
    second order.
  - First order appears only when the cutoff falls between grid points.
  - The packet's wording stands, with that condition stated.
- **A correction to a figure the referee gave in passing.** The referee gave about 1.295 as the true minimum delay gap.
  Moving the scene points along the track as well gives 1.26. Both are above the claimed 1.

**Prior art.** The dossier's components are classical or known in part:
- **The kernel J₁(2Jt)/(Jt): classical.**
  - The original paper, Adelman–Doll 1974, was NOT ACCESSED; it is the source the two READ papers cite.
  - Plyukhin–Schofield, PRE 64 041103 (2001), Eq. (60), prints it as J₀ + J₂ (READ).
  - Lei–Baker–Li, PNAS 2016, harmonic-chain example (READ): at m = K = 1 it is J₁(2t)/t. Their printed formula has a
    dimensional slip.
  - Földi, arXiv:1505.03567, Eq. (24), the transparent-lead kernel (READ).
- **Two-point coupling to a tight-binding chain: known in part.**
  - Same-sign couplings give the kernel J₀ + i^N J_N: Zhang et al., arXiv:2303.16480, Eq. (C7) (READ).
  - Interference removes a band-edge singularity of the spectral density: Wu–An, arXiv:2511.01300, Eqs. (11) and (13)
    (READ).
  - The opposite-sign case 2J₁(z)/z was not found in print. It follows in one line by flipping one sign.
- **Hard truncation versus a positive-definite taper: classical in statistics.**
  - Bickel–Levina, Ann. Statist. 36 (2008), §3.3 (READ).
  - Furrer–Genton–Nychka (2006) (READ).
  - Schur product theorem.
  - For memory kernels in the Langevin setting it is known only in part: Jung–Hanke–Schmid, arXiv:1709.07805, observe
    the negative values and patch them ad hoc (READ).
- **The memory-truncation bound: known in part.**
  - The discrete analogue, with the same (n + 1 − k) weighting, is Jørgensen–Pollock, arXiv:2007.03234, Eq. (22)
    (READ).
  - Semigroup bounds: Zhu–Dominy–Venturi, J. Math. Phys. 59 (2018), Thm 3.3 (READ).
  - The continuous form ∫_T^H (H − τ)|M(τ)| dτ was not found. It is a short Duhamel argument.
- **The plasma feedback equation: confirmed.**
  - Grenier–Nguyen–Rodnianski, arXiv:2004.05979, Eq. (3.2) (READ), exactly.
  - Mouhot–Villani, Eqs. (2.3) and (3.11) (READ), with their kernel equal to −q.

"Not found" is not evidence of novelty. The dossier's contribution is engineering: a short path from the machine-checked
T0E′ to an integrable t^{−4/3} memory bound and a finite-horizon error budget, and an explicit imaging block whose
omission an upper bound can justify. These are candidate consumers (ROADMAP), not breakthroughs, and the dossier
claims none.

## What the dossier found in this repository (all verified by the lead)

1. **`docs/applications.md`: four corrections.**
   - **Line 73** said every stamped statement has a machine-checked proof. That has been false since batch LS was
     stamped.
   - **Line 27** printed the envelope coefficient as 1.547, rounded down from 1.54730…, so as printed it was not an upper
     bound.
   - **Line 28** called t^{−2/3} the decay of return amplitudes. That is the bound uniform over all sites; the return
     amplitude decays faster.
   - **Line 57** showed the D4 closed form only for Disc < 0.
   
   All four are corrected.
2. **The message of commit e814510 says the LS blueprint has "eight parts"; it has nine.** Corrected in
   `docs/proof-LS.md`. Pushed history is not rewritten.
3. **The I3 interface check runs up to order 60 on a periodic grid with 49 sites per axis.** The lead computed the
   periodic-image contribution exactly: at most 1.2·10⁻⁴¹. The PASS stands, and a note is added to the record.
4. **The replay of e814510 was not isolated (lessons 28).** The lead had proposed to disclose this rather than rerun.
   - The reviewer pointed out that lessons 28 states its rule without exception, so disclosure would have been an
     exception, not compliance. The lead agrees.
   - That run was then cut off by a container restart during the comparator step. Its partial log is kept
     (`docs/replay/2026-11-12-session10-e814510-partial.txt`).
   - The acceptance record will be an isolated replay of the commit that records these answers.
5. **The dossier said "six probes"; the session record shows eleven Lean runs** of four probe files, 23:14:12 to
   23:17:40 UTC. The lead's own earlier count, relayed to the reviewer, was wrong.

## AI-use disclosure

- The dossier was produced with ChatGPT (GPT-6 Astra Pro), as the dossier itself states; the lead has not verified the
  version. Its own assistants reviewed it; those share its model family and context.
- The lead, the referee and the prior-art agent are Claude instances. Agreement between them is not independent
  confirmation.
- Nothing here is machine-checked.

# 4. Expected impact and risks

## 4.1 Expected impact

- **For users of the EuroHPC quantum systems.** A benchmark whose ideal output is certified, not simulated on trust:
  a reference table for chains of any length and any time, a proved envelope for the peak population, and an exactly
  computed Trotter error in the tested sector. It is reusable without the project's involvement. Evidence that the
  reference exists: `numerics/results-unlock-register-values-2026-11-16.txt`.
- **For verified mathematics.** A worked case of a machine-checked theorem carried to a measurement: frozen statement,
  kernel replay, certified numerics, registered protocol, raw data. The pieces that exist are listed in
  `docs/STATUS.md` and `docs/prereg/LEDGER.md`; the hardware step would be the first.
- **For the library.** A consumer outside mathematics. The roadmap freezes the public interface only after consumers
  from different domains have used it (`docs/ROADMAP.md`, item I5).
- **Limits of the claim.** No new physics is expected. The measured quantity has been measured before on other
  platforms. The value is in the method and in a public, certified reference.

## 4.2 Risks

| Risk | Likelihood | Consequence | Mitigation |
|---|---|---|---|
| the applicant is not eligible (no employing organisation) | unknown; the rules read do not say | no application | settle before drafting further; fallbacks are a free commercial tier for a pilot and a rolling mathematics fund (`docs/funding/00-call-findings.md`) |
| the portal form asks for fields these drafts do not cover | likely in detail | rework under time pressure | the owner copies the field list early; the sections are short and modular |
| hardware noise swamps the signal at 17 layers on 9 qubits | PLAUSIBLE: published gate-based chain experiments found are 4 to 5 sites | the main runs are inconclusive | the 5-qubit control and the short times are registered as the fallback; post-selection on one excitation; the kept fraction is reported |
| the native gate set differs from the assumed one | unknown until `[CALIBRATION-DATA]` is read | more two-qubit gates per layer | the registered rule enlarges the Trotter step; the error is computed exactly beforehand |
| the finite-chain link to the infinite-lattice theorem stays unproved in Lean | possible | the "machine-checked" label covers the infinite lattice only | stated in the scientific case; the predictions are computed for the finite chain directly and do not depend on it |
| a reviewer sees a device benchmark, not science | possible | a lower relevance judgement | the case says plainly what is and is not new; the call's own purpose is testing a method |
| all proof review so far is by AI referees of one model family | certain (`docs/policy.md`) | a statement could be mis-stated without detection | six-kernel replay covers the proofs, not the fidelity of statements; the tested statement's numerical content is cross-checked by two independent certified computations |
| the cut-off is missed | possible | one month's delay if monthly cut-offs continue (not confirmed for 2027) | the package is modular; the registration can be done at leisure before the next cut-off |

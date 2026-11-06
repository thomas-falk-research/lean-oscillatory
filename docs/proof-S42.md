# S4.2 proof route (the D4 limit t^{2/3} ∫ e^{itφ} A → c_C A(0))

Statement: `OscInt.Statements.D4LimitStatement`. New blueprint parts E1–E3: `Blueprint/D4LimitS42.lean`; reused:
the S4.1′ parts D1–D9 (proved), S2.1/S3 (`OscInt.nonStationary`, `OscInt.fold`), and the S4.3 results (convergence
of `cosMomentPartial`, integrability of |C(cos θ, sin θ)|^{−2/3}). Assembly: `OscInt.D4.d4Limit_of`
(`OscInt/D4/LimitAssembly.lean`).

Notation: φ is C⁴ with φ(0) = 0, ∇φ(0) = 0, D²φ(0) = 0 (so φ is its own normalisation), C its cubic part with
Disc C ≠ 0, Ψ_ε = `rescale φ ε` (Ψ_ε(w) = ε^{−3}φ(εw), Ψ₀ = C), 𝒜 the max-norm annulus 1/2 ≤ ‖z‖ ≤ 2.

## Step 0 (as in S4.1′). The gauge gives ε₀ ∈ (0, 1] with FoldOrNondeg(Ψ_ε) on 𝒜 for ε ∈ [0, ε₀]; S3 on
(Λ = [0, ε₀], 𝒜, K′ = B̄(0, 1)) gives C₃; a cut-off χ (D7, made even by χ ↦ (χ + χ(−·))/2, which keeps all D7
properties); β = χ − χ(2·), tsupport β ⊆ 𝒜, amplitude constant C_β (F2b). **Piece bound** (from the S4.1′ assembly,
with linear term 0): for amplitudes with bound (2, B̄(0, ε₀), M), 0 < ε ≤ ε₀ and tε³ ≥ 1,
|∫ e^{itφ} β(·/ε) A| ≤ C₃ C_β M ε² (tε³)^{−5/6}. Put δ := ε₀/2.

## Step 1. Split at scale ρ = R t^{−1/3} (R ≥ 1 fixed for now). Let N be least with 2^N ρ ≥ δ (E3; scales ε_{j+1} = 2^{j+1}ρ, j < N). On B̄(0, δ):
χ(κ/ρ) + Σ_{j=1}^{N} β(κ/(2^j ρ)) = χ(κ/(2^N ρ)) = 1 (telescoping, 2/ε_j = 1/ε_{j−1}). So
∫ e^{itφ}A = ∫ e^{itφ} χ(·/ρ) A + Σ_{j=1}^{N} ∫ e^{itφ} β(·/ε_j) A, ε_j = 2^j ρ.

## Step 2. Outer pieces. ε_j ≤ 2^N ρ < 2δ = ε₀ for j ≤ N (minimality of N), and tε_j³ = 2^{3j}R³ ≥ 1. The piece bound
and E3 give Σ_j ≤ C₃ C_β M Σ_j ε_j²(tε_j³)^{−5/6} = C₃ C_β M t^{−2/3} R^{−1/2} Σ_{j≥1} 2^{−j/2} ≤ 3 C₃ C_β M R^{−1/2} t^{−2/3}.

## Step 3. Inner piece. Substitute κ = s w, s = t^{−1/3} (F1c with L = s·id, |det| = s²): t s³ = 1, so
t^{2/3} ∫ e^{itφ(κ)} χ(κ/ρ) A(κ) dκ = ∫ e^{iΨ_s(w)} χ(w/R) A(s w) dw. As t → ∞, s → 0, and (E2: dominated convergence;
(s, w) ↦ Ψ_s(w) is continuous by D2, the integrand is bounded by sup|A|·1_{‖w‖ ≤ 2R}) this tends to
A(0) · L(R), L(R) := ∫ e^{iC(w)} χ(w/R) dw.

## Step 4. Polar evaluation (E1): L(R) → c_C as R → ∞. Since χ is even, w ↦ −w gives L(R) = conj L(R), so
L(R) = ∫ cos(C(w)) χ(w/R) dw. In polar coordinates w = r ω(θ) (`integral_comp_polarCoord_symm`), with
g(θ) = C(ω(θ)), ψ_θ(ρ) = χ(ρ ω(θ)):
  L(R) = ∫ dθ ∫₀^∞ cos(r³ g(θ)) ψ_θ(r/R) r dr.
For g(θ) ≠ 0 substitute u = r³|g(θ)| (cos is even, so the sign of g does not matter):
  inner = (1/3)|g|^{−2/3} ∫₀^∞ cos u · u^{−1/3} η_θ(u/Λ) du, η_θ(v) = ψ_θ(v^{1/3}), Λ = |g| R³.
η_θ = 1 on [0, 1] (ψ_θ = 1 on [0, 1] because ‖ρω‖ ≤ ρ), η_θ = 0 on [(2√2)³, ∞), |η_θ′| ≤ B on [1, ∞) uniformly in θ.
1D lemma: for such η, ∫₀^∞ cos u u^{−1/3} η(u/Λ) du → cosMoment as Λ → ∞, and is bounded uniformly in Λ > 0 and θ:
for Λ ≤ 1 by ∫₀^{KΛ} u^{−1/3} ≤ (3/2)K^{2/3}; for Λ ≥ 1 by one integration by parts (C1 of S4.3), the boundary
terms vanish, the main term is (1/3)∫ sin u u^{−4/3} η(u/Λ) (bounded by (1/3)∫₀^∞|sin u|u^{−4/3} < ∞, tends to
(1/3)S = cosMoment by dominated convergence), the derivative term is ≤ Λ^{−1}∫ u^{−1/3}|η′(u/Λ)| du ≤ B K Λ^{−1/3} → 0.
Then dominated convergence in θ (bound const·|g|^{−2/3}, integrable by S4.3; the zeros of g are finitely many, a
null set) gives L(R) → (1/3) cosMoment ∫ |g|^{−2/3} dθ = d4Constant. (Angular range: polar coordinates use
θ ∈ (−π, π); g is 2π-periodic, so ∫_{−π}^{π} = ∫₀^{2π}.)

## Step 5. Combine. |t^{2/3}∫e^{itφ}A − c_C A(0)| ≤ 3C₃C_βM R^{−1/2} + |I_R(t) − A(0)L(R)| + |A(0)||L(R) − c_C|
(using t^{2/3} times the outer bound). Given η > 0 choose R with the first and third terms < η/3, then t₀ with the
second < η/3 for t ≥ t₀ (Step 3). Hence the limit. δ = ε₀/2 depends only on φ, as the statement requires.

## Revision after the route referee (`review/2026-11-06-S42-proof-route.md`, 2026-11-06; overrides the text above)
Verdict: route correct, E1–E3 TRUE, no BLOCKER. MAJOR 1 (piece bound not a part): resolved in the assembly —
`OscInt.D4.exists_piece_bound` (`OscInt/D4/LimitAssembly.lean`) proves it for any D7-type cut-off and every
ε ∈ (0, ε₀], with constant max(C₃, 0)·C_β ≥ 0 (also NIT 7); the whole assembly `d4Limit_of` is machine-checked
against E1–E3. MINOR 2: E1's 1D step is replaced by the radial identity E1a,
λ^{2/3}∫₀^K cos(λr³)ψ(r) r dr = −(1/3)∫₁^K ψ′(ρ) cosMomentPartial(λρ³) dρ (ψ = −∫_r^K ψ′, Fubini, u = λr³ on
[0, ρ]), so no cube-root profile and no case split are needed; cosMomentPartial is continuous and convergent,
hence bounded on [0, ∞), which gives the θ-uniform bound and, by dominated convergence, the limit cosMoment/3.
MINOR 3: the null set of zeros is part E1c (from `OscInt.D4.circleNondeg`). §3: E1 is split into E1a (radial
identity), E1b (polar reduction, θ ∈ (−π, π), radius 2K₀R), E1c (zeros null), E1d (combination: rescaling
r = Rρ with R²(|g|R³)^{−2/3} = |g|^{−2/3}, sup|ψ_θ′| ≤ sup‖Dχ‖, dominated convergence along `atTop`, periodic shift
to [0, 2π]). MINOR 4 (tε³ ≥ 1 in E3) and NIT 6 (`cubicPoly` vs `cubicForm`) are handled in the assembly.

import OscInt.Statements.PeriodicAnalytic

/-!
# Batch FR: the Schrödinger group on a ring of `N` sites and on an open chain of `M` sites (statements only)

Mathematics: `docs/statements.md`, "Batch FR". Written, stamped and blind-reviewed before any Lean proof of these
statements exists (`CONTRIBUTING.md`; `docs/lessons.md`, rule 1).

The equation is `i u′ + Δu = 0` with `(Δu)(x) = u(x + 1) + u(x − 1) − 2u(x)`, as in batch LS, on three graphs: the
line `ℤ` (kernel `lineKernel`, batch LS in one dimension), the ring `ℤ/N` (functions on `ℤ` of period `N`; kernel
`ringKernel`) and the open chain of the sites `1, …, M` with the Dirichlet condition `u(0) = u(M + 1) = 0`
(kernel `chainKernel`).
* FR-K `RingKernelStatement`: the ring kernel solves the equation in the site variable, is the unit datum at time 0
  and has period `N`.
* FR-U `RingUniqueStatement`: every solution of period `N` is the kernel sum of its datum over one period.
* FR-S `RingCosetSumStatement`: the ring kernel is the line kernel summed over a coset of `Nℤ` (method of images).
* FR-P `RingFiniteSizeStatement`: `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every `η > 0`.
* FC-K `ChainKernelStatement`: the chain kernel solves the equation, vanishes at the two walls and is the unit datum.
* FC-U `ChainUniqueStatement`: every solution on the chain is the kernel sum of its datum.
* FC-P `ChainFiniteSizeStatement`: the chain kernel is the line kernel up to the two nearest images:
  `|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`.

Modelling choices: sites are integers; a function on the ring is a function on `ℤ` of period `N`; a function on the
chain is a function on `ℤ` constrained at `0, …, M + 1` only; time derivatives are taken site by site
(`HasDerivAt` of `s ↦ u s x`), which for finitely many sites is the derivative of the vector.
-/

namespace OscInt.Statements

/-- The kernel of `i u′ + Δu = 0` on the line `ℤ`: `G(t, n) = (2π)^{−1} e^{−2it} I(2t, n)`. -/
noncomputable def lineKernel (t : ℝ) (n : ℤ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.exp (↑(-(2 * t)) * Complex.I) * latticeKernel1 (2 * t) (n : ℝ)

/-- The kernel on the ring of `N` sites: `R_N(t, r) = N^{−1} Σ_{j<N} e^{i(2t(cos k_j − 1) + r k_j)}`, `k_j = 2πj/N`. -/
noncomputable def ringKernel (N : ℕ) (t : ℝ) (r : ℤ) : ℂ :=
  ((N : ℝ) : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
    Complex.exp (↑(2 * t * (Real.cos (2 * Real.pi * (j : ℝ) / (N : ℝ)) - 1) +
      (r : ℝ) * (2 * Real.pi * (j : ℝ) / (N : ℝ))) * Complex.I)

/-- The kernel on the open chain of the sites `1, …, M`: the odd reflection of the ring of `2(M + 1)` sites,
`C_M(t; x, y) = R_{2(M+1)}(t, x − y) − R_{2(M+1)}(t, x + y)`. -/
noncomputable def chainKernel (M : ℕ) (t : ℝ) (x y : ℤ) : ℂ :=
  ringKernel (2 * (M + 1)) t (x - y) - ringKernel (2 * (M + 1)) t (x + y)

/-- **FR-K** The ring kernel solves `i ∂_t R + ΔR = 0` in the site variable, equals the unit datum of the ring at
`t = 0` (1 on `Nℤ`, 0 elsewhere) and has period `N`. -/
def RingKernelStatement : Prop :=
  ∀ (N : ℕ) (t : ℝ) (r : ℤ), 0 < N →
    HasDerivAt (fun s : ℝ => ringKernel N s r)
      (Complex.I * (ringKernel N t (r + 1) + ringKernel N t (r - 1) - 2 * ringKernel N t r)) t ∧
    ringKernel N 0 r = (if (N : ℤ) ∣ r then 1 else 0) ∧
    ringKernel N t (r + (N : ℤ)) = ringKernel N t r

theorem statement_pin_RingKernel : RingKernelStatement = RingKernelStatement := rfl

/-- **FR-U** Every solution of period `N` of `i u′ + Δu = 0` is the kernel sum of its datum over one period:
`u(t, x) = Σ_{y<N} R_N(t, x − y) u(0, y)`. -/
def RingUniqueStatement : Prop :=
  ∀ (N : ℕ) (u : ℝ → ℤ → ℂ), 0 < N → (∀ (t : ℝ) (x : ℤ), u t (x + (N : ℤ)) = u t x) →
    (∀ (t : ℝ) (x : ℤ), HasDerivAt (fun s : ℝ => u s x) (Complex.I * (u t (x + 1) + u t (x - 1) - 2 * u t x)) t) →
    ∀ (t : ℝ) (x : ℤ), u t x = ∑ y ∈ Finset.range N, ringKernel N t (x - (y : ℤ)) * u 0 (y : ℤ)

theorem statement_pin_RingUnique : RingUniqueStatement = RingUniqueStatement := rfl

/-- **FR-S** Method of images: the ring kernel is the line kernel summed over the coset `r + Nℤ`. -/
def RingCosetSumStatement : Prop :=
  ∀ (N : ℕ) (t : ℝ) (r : ℤ), 0 < N →
    HasSum (fun m : ℤ => lineKernel t (r + m * (N : ℤ))) (ringKernel N t r)

theorem statement_pin_RingCosetSum : RingCosetSumStatement = RingCosetSumStatement := rfl

/-- **FR-P** Finite-size error of the ring: `|R_N(t, r) − G(t, r)| ≤ 2 e^{2|t| sinh η} cosh(rη) / (e^{ηN} − 1)` for every
`η > 0`. -/
def RingFiniteSizeStatement : Prop :=
  ∀ (N : ℕ) (t η : ℝ) (r : ℤ), 0 < N → 0 < η →
    ‖ringKernel N t r - lineKernel t r‖ ≤
      2 * Real.exp (2 * |t| * Real.sinh η) * Real.cosh ((r : ℝ) * η) / (Real.exp (η * (N : ℝ)) - 1)

theorem statement_pin_RingFiniteSize : RingFiniteSizeStatement = RingFiniteSizeStatement := rfl

/-- **FC-K** The chain kernel solves the equation in the site variable, vanishes at the walls `x = 0` and
`x = M + 1`, and is the unit datum at `t = 0` on the sites `1, …, M`. -/
def ChainKernelStatement : Prop :=
  ∀ (M : ℕ) (t : ℝ) (x y : ℤ), 1 ≤ y → y ≤ (M : ℤ) →
    HasDerivAt (fun s : ℝ => chainKernel M s x y)
      (Complex.I * (chainKernel M t (x + 1) y + chainKernel M t (x - 1) y - 2 * chainKernel M t x y)) t ∧
    chainKernel M t 0 y = 0 ∧ chainKernel M t ((M : ℤ) + 1) y = 0 ∧
    (1 ≤ x → x ≤ (M : ℤ) → chainKernel M 0 x y = (if x = y then 1 else 0))

theorem statement_pin_ChainKernel : ChainKernelStatement = ChainKernelStatement := rfl

/-- **FC-U** Every solution of `i u′ + Δu = 0` on the open chain `1, …, M` with `u = 0` at the walls `0` and `M + 1`
is the kernel sum of its datum: `u(t, x) = Σ_{y=1}^{M} C_M(t; x, y) u(0, y)`. -/
def ChainUniqueStatement : Prop :=
  ∀ (M : ℕ) (u : ℝ → ℤ → ℂ), (∀ t : ℝ, u t 0 = 0 ∧ u t ((M : ℤ) + 1) = 0) →
    (∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      HasDerivAt (fun s : ℝ => u s x) (Complex.I * (u t (x + 1) + u t (x - 1) - 2 * u t x)) t) →
    ∀ (t : ℝ) (x : ℤ), 1 ≤ x → x ≤ (M : ℤ) →
      u t x = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), chainKernel M t x y * u 0 y

theorem statement_pin_ChainUnique : ChainUniqueStatement = ChainUniqueStatement := rfl

/-- **FC-P** Finite-size error of the open chain: for sites `1 ≤ x, y ≤ M` and every `η > 0`,
`|C_M(t; x, y) − G(t, x − y)| ≤ e^{2|t| sinh η} (e^{−(x+y)η} + 2 (cosh((x−y)η) + cosh((x+y)η)) / (e^{2(M+1)η} − 1))`. -/
def ChainFiniteSizeStatement : Prop :=
  ∀ (M : ℕ) (t η : ℝ) (x y : ℤ), 0 < η → 1 ≤ x → x ≤ (M : ℤ) → 1 ≤ y → y ≤ (M : ℤ) →
    ‖chainKernel M t x y - lineKernel t (x - y)‖ ≤
      Real.exp (2 * |t| * Real.sinh η) *
        (Real.exp (-(((x + y : ℤ) : ℝ) * η)) +
          2 * (Real.cosh (((x - y : ℤ) : ℝ) * η) + Real.cosh (((x + y : ℤ) : ℝ) * η)) /
            (Real.exp (2 * ((M : ℝ) + 1) * η) - 1))

theorem statement_pin_ChainFiniteSize : ChainFiniteSizeStatement = ChainFiniteSizeStatement := rfl

end OscInt.Statements

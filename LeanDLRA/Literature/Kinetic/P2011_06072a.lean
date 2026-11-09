import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.OpenProblems.Conservation.Part3c
import LeanDLRA.Stability.Conservation

/-!
# HOLO conservation for low-rank transport (arXiv 2011.06072)

Peng, McClarren, *A high-order / low-order (HOLO) algorithm for preserving conservation in
time-dependent low-rank transport calculations*. This module proves the conservation argument of the
paper at all the levels at which the paper writes its low-order (LO) system: the PDE system (12),
(16) on a box in any dimension, for every closure `γ` (`IsLOSolution.hasDerivAt_total`,
`IsLOSolution.total_eq`); the forward Euler system (24) with true derivatives on a rectangle
(`IsLOFieldStep.integral_balance`); (24) for arbitrary spatial operators
(`LOData.IsLOStep.map_balance`, `LOData.map_conserved`, `LOData.inner_conserved`); and the lumped
bilinear discontinuous operators of Eq. (32) on a periodic mesh, for which the flux-freeness assumed
in the abstract theorems is derived (`Grid.mass_divX`, `Grid.mass_divZ`, `Grid.mass_forward_euler`,
`Grid.lo_mass_conserved`). It also proves that the closure (23) reproduces the high-order (HO) first
moments and is the only closure that does (`LOData.IsLOStep.reproduces`,
`LOData.IsLOStep.eq_closure`), that the substitution (21) turns (12), (16) into the `P₁` form
(`LOData.isFluxStep_iff`), the properties of the conservation fix (25) with the angular basis fixed
(`isMomentFix_iff`, `exists_isLeastSquaresFix`, `exists_isMomentFix_iff`,
`forall_exists_isMomentFix_iff`, `minNormFix_spec`, `rank_fix_le`, `rightProj_fix`,
`fix_eq_consTrunc`), and, as the main theorems, that Algorithm 2 as a whole is conservative
(`holo_conservative`, and `Grid.holo_mass_conserved` for the fully discrete scheme), which the paper
only observes numerically.

## Differences from the paper

* **A false reading of (25).** "The match in (25) is exact iff the `r × 3` moment matrix has rank 3"
  (the statement this module was asked to prove; the paper itself only says least squares) is false
  for a fixed target (`exact_without_rank_three`), and the exact criterion is
  `exists_isMomentFix_iff`. Rank 3 is what is needed for *every* target at once
  (`forall_exists_isMomentFix_iff`, which is `holo_correction_solvable_iff` of the library).
* Rank 3 is more than Algorithm 2 needs. By the closure (23) the DLR prediction already has the LO
  first moments, so the defect in (25) lies in `φ₀⁰` alone. The sharp condition is that `(1, 0, 0)`
  lies in the row space of the moment matrix (`exists_isMomentFix_of_e₀`,
  `e₀_mem_of_exists_isMomentFix`). `holo_conservative` assumes this at every step. It is not
  automatic, and the paper does not address it: it holds if the angular basis contains the moment
  directions (`rank_momentMatrix_of_contains`), which Algorithm 2 does not enforce. If it fails, the
  least-squares fix is not exact and `holo_conservative` says nothing.
* **Misprints in the paper.** (22)–(24) print `σ_t φ₀⁰` in both current equations. But (16) and (21)
  give `σ_t φ₁⁰` and `σ_t φ₁¹` (`LOData.isFluxStep_iff`), in agreement with the matrix `C` of (28).
  All theorems on (23), (24) take these removal terms as a parameter `R`, so they cover the printed
  form (`LOData.printedRemoval`) and the correct one (`LOData.currentRemoval`). The last row of
  `A_x` in (28) prints `-√(1/3)` where (22) has `-√(1/6)`; (21) confirms `√(1/6)`, which we use.
  The line before (32) prints `- L_x u` with `L_x = -∫∫ (∂_x B) Bᵀ`; this module formalizes the
  lumped operator of (32) as printed and does not check that sign. Conservation depends on
  none of these points.
* "Conservative" in the paper means the balance law: `∫ φ` changes only through boundary fluxes,
  absorption and sources. Exact constancy needs these to vanish (`IsLOSolution.total_eq`,
  `LOData.map_conserved`).
* `IsLOSolution`: the fields are `C¹` in `(t, r)` on all of `ℝ × ℝⁿ⁺¹`, and the domain is a box.
* `LOData`: the operators are arbitrary maps, which covers limiters and every discretization;
  only `LOData.isFluxStep_iff` needs them homogeneous, and it is stated with `c = 1`, as in the
  paper.
* `Grid`: the mesh is periodic and conforming and the numerical traces are single valued. The paper
  specifies neither its numerical flux nor this property. On a mesh with physical boundaries the
  boundary fluxes stay in `LOData.IsLOStep.map_balance`, which assumes nothing on `ℓ`.
* The DLR step (Algorithm 1) is an arbitrary prediction `Kp Vpᵀ`: nothing about it is used, which is
  the point of the method.
* Not formalized: the angular discretization (17)–(20) beyond the moment formula, the asymptotic
  limit, the QR factorization of `K^new`, the memory counts (26), (27) and the numerical results.
-/

open Set Filter Topology Finset MeasureTheory
open scoped RealInnerProductSpace Matrix Real

namespace LeanDLRA.Literature.P2011_06072

/-! ### The low-order system -/

/-- The three angular moments `(φ₀⁰, φ₁⁰, φ₁¹)` of arXiv 2011.06072, Eq. (21), as elements of a
space `V` of spatial fields. -/
@[ext] structure Moments (V : Type*) where
  /-- The moment `φ₀⁰`, proportional to the scalar flux `φ`. -/
  φ₀₀ : V
  /-- The moment `φ₁⁰`, proportional to the current `J_z`. -/
  φ₁₀ : V
  /-- The moment `φ₁¹`, proportional to the current `J_x`. -/
  φ₁₁ : V

/-- The spatial operators of the low-order system of arXiv 2011.06072, Eq. (24): the derivatives
`∂_z`, `∂_x` and the multiplications by the cross-sections `σ_s`, `σ_t`. They are arbitrary maps
(so that semi-discrete, fully discrete and limited schemes are all covered). -/
structure LOData (V : Type*) where
  /-- The discrete derivative `∂_z`. -/
  Dz : V → V
  /-- The discrete derivative `∂_x`. -/
  Dx : V → V
  /-- Multiplication by `σ_s`. -/
  σs : V → V
  /-- Multiplication by `σ_t`. -/
  σt : V → V

section LO

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem step_iff {Δt : ℝ} (hΔt : Δt ≠ 0) {x y a b : V} :
    (1 / Δt) • (y - x) + a = b ↔ y = x + Δt • (b - a) := by
  constructor
  · intro h
    have : y - x = Δt • (b - a) := by
      rw [← h, add_sub_cancel_right, smul_smul, mul_one_div_cancel hΔt, one_smul]
    rw [← this]; abel
  · rintro rfl
    rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel hΔt, one_smul]; abel

namespace LOData

variable (L : LOData V)

/-- The removal terms of the current equations as printed in arXiv 2011.06072, Eqs. (22)–(24):
`σ_t φ₀⁰` in both equations. -/
def printedRemoval (u : Moments V) : V × V := (L.σt u.φ₀₀, L.σt u.φ₀₀)

/-- The removal terms of the current equations that follow from Eqs. (16), (21) and agree with the
matrix `C` of Eq. (28): `σ_t φ₁⁰` and `σ_t φ₁¹`. -/
def currentRemoval (u : Moments V) : V × V := (L.σt u.φ₁₀, L.σt u.φ₁₁)

/-- **The closure of arXiv 2011.06072, Eq. (23)**, `(γ_z, γ_x)`, computed from the high-order
moments `ho` at `tₙ` and `hoNext` at `tₙ₊₁`. The removal terms `R` are `L.printedRemoval` for the
printed formula. -/
noncomputable def closure (R : Moments V → V × V) (Δt : ℝ) (ho hoNext : Moments V) : V × V :=
  ((1 / Δt) • (hoNext.φ₁₀ - ho.φ₁₀) + √(1 / 3) • L.Dz ho.φ₀₀ + (R ho).1,
   (1 / Δt) • (hoNext.φ₁₁ - ho.φ₁₁) - √(1 / 6) • L.Dx ho.φ₀₀ + (R ho).2)

/-- **The forward Euler low-order system, arXiv 2011.06072, Eq. (24)**, from `u` at `tₙ` to `u'`
at `tₙ₊₁` with closure `γ = (γ_z, γ_x)` and source `Q`. The removal terms `R` of the current
equations are `L.printedRemoval` for the printed formula. -/
structure IsLOStep (R : Moments V → V × V) (Q : V) (Δt : ℝ) (γ : V × V) (u u' : Moments V) :
    Prop where
  eq₀ : (1 / Δt) • (u'.φ₀₀ - u.φ₀₀) + √(1 / 3) • L.Dz u.φ₁₀ - √(2 / 3) • L.Dx u.φ₁₁ =
    (L.σs u.φ₀₀ - L.σt u.φ₀₀) + (1 / (2 * √π)) • Q
  eq₁ : (1 / Δt) • (u'.φ₁₀ - u.φ₁₀) + √(1 / 3) • L.Dz u.φ₀₀ = -(R u).1 + γ.1
  eq₂ : (1 / Δt) • (u'.φ₁₁ - u.φ₁₁) - √(1 / 6) • L.Dx u.φ₀₀ = -(R u).2 + γ.2

/-- The explicit update of Eq. (24). -/
noncomputable def loStep (R : Moments V → V × V) (Q : V) (Δt : ℝ) (γ : V × V) (u : Moments V) :
    Moments V where
  φ₀₀ := u.φ₀₀ + Δt • ((L.σs u.φ₀₀ - L.σt u.φ₀₀) + (1 / (2 * √π)) • Q -
    (√(1 / 3) • L.Dz u.φ₁₀ - √(2 / 3) • L.Dx u.φ₁₁))
  φ₁₀ := u.φ₁₀ + Δt • (-(R u).1 + γ.1 - √(1 / 3) • L.Dz u.φ₀₀)
  φ₁₁ := u.φ₁₁ + Δt • (-(R u).2 + γ.2 + √(1 / 6) • L.Dx u.φ₀₀)

variable {L} {R : Moments V → V × V} {Q : V} {Δt : ℝ} {γ : V × V} {u u' : Moments V}

/-- arXiv 2011.06072, Eq. (24): for `Δt ≠ 0` the low-order system has exactly one solution, the
explicit forward Euler update. -/
theorem isLOStep_iff (hΔt : Δt ≠ 0) : L.IsLOStep R Q Δt γ u u' ↔ u' = L.loStep R Q Δt γ u := by
  constructor
  · intro h
    have h₀ := h.eq₀
    have h₁ := h.eq₁
    have h₂ := h.eq₂
    rw [add_sub_assoc, step_iff hΔt] at h₀
    rw [step_iff hΔt] at h₁
    rw [sub_eq_add_neg, step_iff hΔt, sub_neg_eq_add] at h₂
    exact Moments.ext h₀ h₁ h₂
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [add_sub_assoc, step_iff hΔt]; rfl
    · rw [step_iff hΔt]; rfl
    · rw [sub_eq_add_neg, step_iff hΔt, sub_neg_eq_add]; rfl

/-- **Eq. (24) is globally conservative for every closure** (arXiv 2011.06072, Sec. 3.2, "This
formulation is globally conservative"; Eqs. 12, 16, 24). For every linear functional
`ℓ`, the change of `ℓ φ₀⁰` in one forward Euler step of the low-order system is the flux term plus
the absorption and source terms. The closure `γ` and the removal terms `R` of the current equations
do not enter. Here `ℓ` is arbitrary, and the flux term is kept. -/
theorem IsLOStep.map_balance (h : L.IsLOStep R Q Δt γ u u') (hΔt : Δt ≠ 0) (ℓ : V →ₗ[ℝ] ℝ) :
    ℓ u'.φ₀₀ = ℓ u.φ₀₀ + Δt * (ℓ (L.σs u.φ₀₀ - L.σt u.φ₀₀) + 1 / (2 * √π) * ℓ Q -
      (√(1 / 3) * ℓ (L.Dz u.φ₁₀) - √(2 / 3) * ℓ (L.Dx u.φ₁₁))) := by
  rw [(isLOStep_iff hΔt).1 h]
  simp only [loStep, map_add, map_sub, map_smul, smul_eq_mul]

/-- arXiv 2011.06072, Eq. (24), Eqs. 12, 16, 24: if `ℓ` annihilates the discrete
derivatives (for a suitable `ℓ` this is what "`J` appears in conservative form" means, see
`Grid.mass_divX`), then the flux term vanishes. -/
theorem IsLOStep.map_balance_of_flux_free (h : L.IsLOStep R Q Δt γ u u') (hΔt : Δt ≠ 0)
    (ℓ : V →ₗ[ℝ] ℝ) (hz : ∀ v, ℓ (L.Dz v) = 0) (hx : ∀ v, ℓ (L.Dx v) = 0) :
    ℓ u'.φ₀₀ = ℓ u.φ₀₀ + Δt * (ℓ (L.σs u.φ₀₀ - L.σt u.φ₀₀) + 1 / (2 * √π) * ℓ Q) := by
  rw [h.map_balance hΔt ℓ, hz, hx]; ring

/-- **The linear invariant**, arXiv 2011.06072, Eq. (24), Eqs. 12, 16, 24: a linear
functional that annihilates the discrete derivatives, the absorption `σ_s - σ_t` and the sources
is exactly conserved over any number of forward Euler steps, for arbitrary closures `γ n`
(which may depend on the step) and sources. -/
theorem map_conserved {u : ℕ → Moments V} {Q : ℕ → V} {γ : ℕ → V × V} (hΔt : Δt ≠ 0)
    (h : ∀ n, L.IsLOStep R (Q n) Δt (γ n) (u n) (u (n + 1))) (ℓ : V →ₗ[ℝ] ℝ)
    (hz : ∀ v, ℓ (L.Dz v) = 0) (hx : ∀ v, ℓ (L.Dx v) = 0)
    (ha : ∀ v, ℓ (L.σs v - L.σt v) = 0) (hQ : ∀ n, ℓ (Q n) = 0) (n : ℕ) :
    ℓ (u n).φ₀₀ = ℓ (u 0).φ₀₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [(h n).map_balance_of_flux_free hΔt ℓ hz hx, ha, hQ, ih]; ring

/-- **The closure reproduces the high-order first moments**, arXiv 2011.06072, Eq. (23): if the
low-order and high-order moments agree at `tₙ`, the update (24) with the closure (23) gives the
high-order first moments at `tₙ₊₁`. This holds for any removal terms `R`, in particular for the
printed `L.printedRemoval` and for `L.currentRemoval`. -/
theorem IsLOStep.reproduces (hΔt : Δt ≠ 0) {ho hoNext lo lo' : Moments V} (hlo : lo = ho)
    (h : L.IsLOStep R Q Δt (L.closure R Δt ho hoNext) lo lo') :
    lo'.φ₁₀ = hoNext.φ₁₀ ∧ lo'.φ₁₁ = hoNext.φ₁₁ := by
  subst hlo
  rw [isLOStep_iff hΔt] at h
  subst h
  constructor
  · simp only [loStep, closure]
    have : -(R lo).1 + ((1 / Δt) • (hoNext.φ₁₀ - lo.φ₁₀) + √(1 / 3) • L.Dz lo.φ₀₀ + (R lo).1) -
        √(1 / 3) • L.Dz lo.φ₀₀ = (1 / Δt) • (hoNext.φ₁₀ - lo.φ₁₀) := by abel
    rw [this, smul_smul, mul_one_div_cancel hΔt, one_smul]; abel
  · simp only [loStep, closure]
    have : -(R lo).2 + ((1 / Δt) • (hoNext.φ₁₁ - lo.φ₁₁) - √(1 / 6) • L.Dx lo.φ₀₀ + (R lo).2) +
        √(1 / 6) • L.Dx lo.φ₀₀ = (1 / Δt) • (hoNext.φ₁₁ - lo.φ₁₁) := by abel
    rw [this, smul_smul, mul_one_div_cancel hΔt, one_smul]; abel

/-- **The closure (23) is the only one with this property**, arXiv 2011.06072, Eq. (23) (the paper
only states the formula): if the update (24) from the high-order moments `ho` reproduces the first
moments of `hoNext`, then `γ` is the closure (23). -/
theorem IsLOStep.eq_closure {ho hoNext lo' : Moments V}
    (h : L.IsLOStep R Q Δt γ ho lo') (h₁ : lo'.φ₁₀ = hoNext.φ₁₀) (h₂ : lo'.φ₁₁ = hoNext.φ₁₁) :
    γ = L.closure R Δt ho hoNext := by
  have e₁ := h.eq₁
  have e₂ := h.eq₂
  rw [h₁] at e₁
  rw [h₂] at e₂
  refine Prod.ext ?_ ?_
  · change γ.1 = _ + _ + _
    rw [e₁]; abel
  · change γ.2 = _ - _ + _
    rw [e₂]; abel

/-- The forward Euler form of arXiv 2011.06072, Eqs. (12), (16) with `c = 1` (the paper's choice in
the derivation of (22)), in the variables `φ`, `J_z`, `J_x`, with closure `Γ = (Γ_z, Γ_x)`. -/
structure IsFluxStep (Q : V) (Δt : ℝ) (Γ : V × V) (φ Jz Jx φ' Jz' Jx' : V) : Prop where
  eq12 : (1 / Δt) • (φ' - φ) + L.Dz Jz + L.Dx Jx + L.σt φ = L.σs φ + Q
  eq16z : (1 / Δt) • (Jz' - Jz) + (1 / 3 : ℝ) • L.Dz φ + L.σt Jz = Γ.1
  eq16x : (1 / Δt) • (Jx' - Jx) + (1 / 3 : ℝ) • L.Dx φ + L.σt Jx = Γ.2

private theorem scal₁ : 2 * √(π / 3) = √(1 / 3) * (2 * √π) := by
  rw [show π / 3 = 1 / 3 * π by ring, Real.sqrt_mul (by norm_num)]; ring

private theorem scal₂ : 2 * √(2 * π / 3) = √(2 / 3) * (2 * √π) := by
  rw [show 2 * π / 3 = 2 / 3 * π by ring, Real.sqrt_mul (by norm_num)]; ring

private theorem scal₃ : √(1 / 3) * √(1 / 3) = (1 / 3 : ℝ) :=
  Real.mul_self_sqrt (by norm_num)

private theorem scal₄ : √(2 / 3) * √(1 / 6) = (1 / 3 : ℝ) := by
  rw [← Real.sqrt_mul (by norm_num), show (2 / 3 * (1 / 6) : ℝ) = (1 / 3) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

omit [AddCommGroup V] [Module ℝ V] in
private theorem eq_iff_of_smul [AddCommGroup V] [Module ℝ V] {a : ℝ} (ha : a ≠ 0) {x y x' y' : V}
    (h : x - y = a • (x' - y')) : x = y ↔ x' = y' := by
  rw [← sub_eq_zero (a := x), h, smul_eq_zero_iff_right ha, sub_eq_zero]

/-- **The substitution (21) turns (12), (16) into the `P₁` form (22), (24)**, with the constants
`√(1/3)`, `√(2/3)`, `√(1/6)` of the paper, but with `σ_t φ₁⁰`, `σ_t φ₁¹` (`L.currentRemoval`) in the
current equations instead of the printed `σ_t φ₀⁰`. So the printed removal terms are a misprint;
they also disagree with the matrix `C` of Eq. (28). Stated for the time discrete systems, for
operators `Dz`, `Dx`, `σs`, `σt` that are homogeneous. -/
theorem isFluxStep_iff (hz : ∀ (s : ℝ) v, L.Dz (s • v) = s • L.Dz v)
    (hx : ∀ (s : ℝ) v, L.Dx (s • v) = s • L.Dx v) (hs : ∀ (s : ℝ) v, L.σs (s • v) = s • L.σs v)
    (ht : ∀ (s : ℝ) v, L.σt (s • v) = s • L.σt v) :
    L.IsFluxStep Q Δt ((2 * √(π / 3)) • γ.1, (-(2 * √(2 * π / 3))) • γ.2)
        ((2 * √π) • u.φ₀₀) ((2 * √(π / 3)) • u.φ₁₀) ((-(2 * √(2 * π / 3))) • u.φ₁₁)
        ((2 * √π) • u'.φ₀₀) ((2 * √(π / 3)) • u'.φ₁₀) ((-(2 * √(2 * π / 3))) • u'.φ₁₁) ↔
      L.IsLOStep L.currentRemoval Q Δt γ u u' := by
  have ha : (2 * √π : ℝ) ≠ 0 := by positivity
  have hb : (√(1 / 3) * (2 * √π) : ℝ) ≠ 0 := by positivity
  have hd : (-(√(2 / 3) * (2 * √π)) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < √(2 / 3) * (2 * √π) := by positivity
    linarith
  rw [scal₁, scal₂]
  have e₀ : (1 / Δt) • ((2 * √π) • u'.φ₀₀ - (2 * √π) • u.φ₀₀) +
        L.Dz ((√(1 / 3) * (2 * √π)) • u.φ₁₀) + L.Dx ((-(√(2 / 3) * (2 * √π))) • u.φ₁₁) +
        L.σt ((2 * √π) • u.φ₀₀) - (L.σs ((2 * √π) • u.φ₀₀) + Q) =
      (2 * √π) • ((1 / Δt) • (u'.φ₀₀ - u.φ₀₀) + √(1 / 3) • L.Dz u.φ₁₀ - √(2 / 3) • L.Dx u.φ₁₁ -
        ((L.σs u.φ₀₀ - L.σt u.φ₀₀) + (1 / (2 * √π)) • Q)) := by
    obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁, Q₁ = (1 / (2 * √π) : ℝ) • Q := ⟨_, rfl⟩
    have hQ : Q = (2 * √π) • Q₁ := by rw [hQ₁, smul_smul, mul_one_div_cancel ha, one_smul]
    rw [← hQ₁, hz, hx, hs, ht, hQ]
    module
  have e₁ : (1 / Δt) • ((√(1 / 3) * (2 * √π)) • u'.φ₁₀ - (√(1 / 3) * (2 * √π)) • u.φ₁₀) +
        (1 / 3 : ℝ) • L.Dz ((2 * √π) • u.φ₀₀) + L.σt ((√(1 / 3) * (2 * √π)) • u.φ₁₀) -
        (√(1 / 3) * (2 * √π)) • γ.1 =
      (√(1 / 3) * (2 * √π)) • ((1 / Δt) • (u'.φ₁₀ - u.φ₁₀) + √(1 / 3) • L.Dz u.φ₀₀ -
        (-(L.currentRemoval u).1 + γ.1)) := by
    have e : (1 / 3 : ℝ) • (2 * √π) • L.Dz u.φ₀₀ =
        (√(1 / 3) * √(1 / 3)) • (2 * √π) • L.Dz u.φ₀₀ := by rw [scal₃]
    rw [hz, ht, e]
    simp only [currentRemoval]
    module
  have e₂ : (1 / Δt) • ((-(√(2 / 3) * (2 * √π))) • u'.φ₁₁ - (-(√(2 / 3) * (2 * √π))) • u.φ₁₁) +
        (1 / 3 : ℝ) • L.Dx ((2 * √π) • u.φ₀₀) + L.σt ((-(√(2 / 3) * (2 * √π))) • u.φ₁₁) -
        (-(√(2 / 3) * (2 * √π))) • γ.2 =
      (-(√(2 / 3) * (2 * √π))) • ((1 / Δt) • (u'.φ₁₁ - u.φ₁₁) - √(1 / 6) • L.Dx u.φ₀₀ -
        (-(L.currentRemoval u).2 + γ.2)) := by
    have e : (1 / 3 : ℝ) • (2 * √π) • L.Dx u.φ₀₀ =
        (√(2 / 3) * √(1 / 6)) • (2 * √π) • L.Dx u.φ₀₀ := by rw [scal₄]
    rw [hx, ht, e]
    simp only [currentRemoval]
    module
  constructor
  · rintro ⟨h₀, h₁, h₂⟩
    exact ⟨(eq_iff_of_smul ha e₀).1 h₀, (eq_iff_of_smul hb e₁).1 h₁, (eq_iff_of_smul hd e₂).1 h₂⟩
  · rintro ⟨h₀, h₁, h₂⟩
    exact ⟨(eq_iff_of_smul ha e₀).2 h₀, (eq_iff_of_smul hb e₁).2 h₁, (eq_iff_of_smul hd e₂).2 h₂⟩

end LOData

end LO

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {L : LOData V}
  {R : Moments V → V × V} {Δt : ℝ}

/-- **The linear invariant `⟪c, φ₀⁰⟫` in one step**, arXiv 2011.06072, Eqs. 12, 16, 24: if `c` is
orthogonal to the discrete derivatives, one forward Euler LO step changes `⟪c, φ₀⁰⟫` only by
absorption and sources, for every closure. -/
theorem LOData.IsLOStep.inner_balance {Q : V} {γ : V × V} {u u' : Moments V}
    (h : L.IsLOStep R Q Δt γ u u') (hΔt : Δt ≠ 0) (c : V) (hz : ∀ v, ⟪c, L.Dz v⟫ = 0)
    (hx : ∀ v, ⟪c, L.Dx v⟫ = 0) :
    ⟪c, u'.φ₀₀⟫ = ⟪c, u.φ₀₀⟫ +
      Δt * (⟪c, L.σs u.φ₀₀ - L.σt u.φ₀₀⟫ + 1 / (2 * √π) * ⟪c, Q⟫) :=
  h.map_balance_of_flux_free hΔt (innerₗ V c) hz hx

/-- **The forward Euler LO update conserves the linear invariant `⟪c, φ₀⁰⟫`**, arXiv 2011.06072,
Eqs. 12, 16, 24: if `c` is orthogonal to the discrete derivatives, to the absorption and to the
sources, then `⟪c, φ₀⁰⟫` is constant, for arbitrary closures. -/
theorem LOData.inner_conserved {u : ℕ → Moments V} {Q : ℕ → V} {γ : ℕ → V × V} (hΔt : Δt ≠ 0)
    (h : ∀ n, L.IsLOStep R (Q n) Δt (γ n) (u n) (u (n + 1))) (c : V)
    (hz : ∀ v, ⟪c, L.Dz v⟫ = 0) (hx : ∀ v, ⟪c, L.Dx v⟫ = 0)
    (ha : ∀ v, ⟪c, L.σs v - L.σt v⟫ = 0) (hQ : ∀ n, ⟪c, Q n⟫ = 0) (n : ℕ) :
    ⟪c, (u n).φ₀₀⟫ = ⟪c, (u 0).φ₀₀⟫ :=
  LOData.map_conserved hΔt h (innerₗ V c) hz hx ha hQ n

end Inner

/-! ### The bilinear discontinuous discretization, Eq. (32) -/

/-- A logically rectangular periodic mesh of cells `κ` (as for Eq. (30)): `east` and `north` are the
right and the top neighbour, `dx`, `dz` the cell sizes `Δx_k`, `Δz_k`. Neighbours across a vertical
face have the same `Δz`, neighbours across a horizontal face the same `Δx`, so that the mesh is
conforming. -/
structure Grid (κ : Type*) where
  /-- The right neighbour of a cell. -/
  east : Equiv.Perm κ
  /-- The top neighbour of a cell. -/
  north : Equiv.Perm κ
  /-- The cell width `Δx_k`. -/
  dx : κ → ℝ
  /-- The cell height `Δz_k`. -/
  dz : κ → ℝ
  dx_ne : ∀ k, dx k ≠ 0
  dz_ne : ∀ k, dz k ≠ 0
  dz_east : ∀ k, dz (east k) = dz k
  dx_north : ∀ k, dx (north k) = dx k

/-- The first within-cell matrix of arXiv 2011.06072, Eq. (32). -/
def volX : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 0, 0; -1, -1, 0, 0; 0, 0, -1, -1; 0, 0, 1, 1]

/-- The second within-cell matrix of arXiv 2011.06072, Eq. (32). -/
def volZ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 1, 0; 0, -1, -1, 0; -1, 0, 0, -1]

/-- The periodic uniform grid on `ZMod Nx × ZMod Nz`, the example behind the abstract `Grid`. -/
def periodicGrid (Nx Nz : ℕ) (hx hz : ℝ) (hhx : hx ≠ 0) (hhz : hz ≠ 0) :
    Grid (ZMod Nx × ZMod Nz) where
  east := Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl _)
  north := Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1)
  dx _ := hx
  dz _ := hz
  dx_ne _ := hhx
  dz_ne _ := hhz
  dz_east _ := rfl
  dx_north _ := rfl

namespace Grid

variable {κ : Type*} (G : Grid κ)

/-- The `∂_x`-part of the lumped BLD operator of arXiv 2011.06072, Eq. (32), for one scalar field
with nodal values `f k i` in the cell `k`, node `i + 1`.

`T k 0`, `T k 1` are the values of the numerical trace on the right face of the cell `k` at its
lower and upper node. They stand for both `u^{x+}_{k,2}`, `u^{x+}_{k,3}` and `u^{x-}_{k',1}`,
`u^{x-}_{k',4}` in the right neighbour `k'`: the numerical flux is single valued. -/
noncomputable def divX (f : κ → Fin 4 → ℝ) (T : κ → Fin 2 → ℝ) : κ → Fin 4 → ℝ := fun k i =>
  2 / G.dx k * (![-T (G.east.symm k) 0, T k 0, T k 1, -T (G.east.symm k) 1] : Fin 4 → ℝ) i +
    1 / G.dx k * (volX *ᵥ f k) i

/-- The `∂_z`-part of the lumped BLD operator of arXiv 2011.06072, Eq. (32).

`T k 0`, `T k 1` are the values of the numerical trace on the top face of the cell `k` at its left
and right node. They stand for both `u^{z+}_{k,4}`, `u^{z+}_{k,3}` and `u^{z-}_{k',1}`,
`u^{z-}_{k',2}` in the top neighbour `k'`. -/
noncomputable def divZ (f : κ → Fin 4 → ℝ) (T : κ → Fin 2 → ℝ) : κ → Fin 4 → ℝ := fun k i =>
  2 / G.dz k * (![-T (G.north.symm k) 0, -T (G.north.symm k) 1, T k 1, T k 0] : Fin 4 → ℝ) i +
    1 / G.dz k * (volZ *ᵥ f k) i

variable [Fintype κ]

/-- The total mass `∑ₖ (Δx_k Δz_k / 4) ∑ᵢ u_{k,i}`, that is the integral over the mesh of the
bilinear function with basis (30), equivalently the lumped mass matrix of Sec. 4.1. -/
noncomputable def mass : (κ → Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ k, G.dx k * G.dz k / 4 * ∑ i, w k i
  map_add' w w' := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring

/-- The formula of the mass of arXiv 2011.06072, Sec. 4.1. -/
theorem mass_apply (w : κ → Fin 4 → ℝ) : G.mass w = ∑ k, G.dx k * G.dz k / 4 * ∑ i, w k i := rfl

/-- **The BLD operator (32) is in conservative form**, `∂_x`-part (arXiv 2011.06072, Eq. (32); the
paper does not state this). On a periodic mesh the mass of the discrete derivative vanishes, for
all nodal values and all single valued numerical traces. -/
theorem mass_divX (f : κ → Fin 4 → ℝ) (T : κ → Fin 2 → ℝ) : G.mass (G.divX f T) = 0 := by
  have key : ∀ k, G.dx k * G.dz k / 4 * ∑ i, G.divX f T k i =
      G.dz k / 2 * (T k 0 + T k 1) -
        G.dz (G.east.symm k) / 2 * (T (G.east.symm k) 0 + T (G.east.symm k) 1) := by
    intro k
    have hd := G.dx_ne k
    have hz : G.dz (G.east.symm k) = G.dz k := by
      have := G.dz_east (G.east.symm k)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    rw [hz]
    simp [divX, Fin.sum_univ_four, volX, Matrix.mulVec, dotProduct]
    field_simp
    ring
  have hs : ∑ k, G.dz (G.east.symm k) / 2 * (T (G.east.symm k) 0 + T (G.east.symm k) 1) =
      ∑ k, G.dz k / 2 * (T k 0 + T k 1) :=
    Equiv.sum_comp G.east.symm fun k => G.dz k / 2 * (T k 0 + T k 1)
  rw [mass_apply, Finset.sum_congr rfl fun k _ => key k, Finset.sum_sub_distrib, hs, sub_self]

/-- **The BLD operator (32) is in conservative form**, `∂_z`-part (arXiv 2011.06072, Eq. (32); the
paper does not state this). -/
theorem mass_divZ (f : κ → Fin 4 → ℝ) (T : κ → Fin 2 → ℝ) : G.mass (G.divZ f T) = 0 := by
  have key : ∀ k, G.dx k * G.dz k / 4 * ∑ i, G.divZ f T k i =
      G.dx k / 2 * (T k 0 + T k 1) -
        G.dx (G.north.symm k) / 2 * (T (G.north.symm k) 0 + T (G.north.symm k) 1) := by
    intro k
    have hd := G.dz_ne k
    have hz : G.dx (G.north.symm k) = G.dx k := by
      have := G.dx_north (G.north.symm k)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    rw [hz]
    simp [divZ, Fin.sum_univ_four, volZ, Matrix.mulVec, dotProduct]
    field_simp
    ring
  have hs : ∑ k, G.dx (G.north.symm k) / 2 * (T (G.north.symm k) 0 + T (G.north.symm k) 1) =
      ∑ k, G.dx k / 2 * (T k 0 + T k 1) :=
    Equiv.sum_comp G.north.symm fun k => G.dx k / 2 * (T k 0 + T k 1)
  rw [mass_apply, Finset.sum_congr rfl fun k _ => key k, Finset.sum_sub_distrib, hs, sub_self]

/-- **Global conservation of the fully discrete low-order scheme with arbitrary numerical fluxes**
(arXiv 2011.06072, first row of Eq. (32) with forward Euler in time, using `A_x`, `A_z`, `C`, `S` of
Eq. (28)). The traces `Tz`, `Tx` of `J_z`, `J_x` are arbitrary, so they may depend on all unknowns,
as for an upwind flux of the system, and on a limiter (Eqs. (37)–(40)). The closure only enters the
equations of `J_z` and `J_x`. The sources are the node values `Q k i / (2 √π)`. The mesh is
periodic; with physical boundaries the boundary fluxes remain (see
`LOData.IsLOStep.map_balance`). -/
theorem mass_forward_euler {Δt : ℝ} (hΔt : Δt ≠ 0) {φ φ' Jz Jx Q : κ → Fin 4 → ℝ}
    {Tz Tx : κ → Fin 2 → ℝ} {σs σt : κ → ℝ}
    (h : ∀ k i, (φ' k i - φ k i) / Δt + √(1 / 3) * G.divZ Jz Tz k i - √(2 / 3) * G.divX Jx Tx k i =
      (σs k - σt k) * φ k i + 1 / (2 * √π) * Q k i) :
    G.mass φ' = G.mass φ + Δt * G.mass fun k i => (σs k - σt k) * φ k i + 1 / (2 * √π) * Q k i := by
  have e : φ' = φ + Δt • ((fun k i => (σs k - σt k) * φ k i + 1 / (2 * √π) * Q k i) -
      √(1 / 3) • G.divZ Jz Tz + √(2 / 3) • G.divX Jx Tx) := by
    funext k i
    have h' := h k i
    have h'' : (φ' k i - φ k i) / Δt = (σs k - σt k) * φ k i + 1 / (2 * √π) * Q k i -
        √(1 / 3) * G.divZ Jz Tz k i + √(2 / 3) * G.divX Jx Tx k i := by linarith
    rw [div_eq_iff hΔt] at h''
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  rw [e]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, mass_divX, mass_divZ]
  ring

/-- The low-order operators of the BLD scheme (32): the discrete derivatives of each scalar moment
with numerical traces `Tz`, `Tx`, which are arbitrary (nonlinear) functions of that moment. -/
noncomputable def loData (Tz Tx : (κ → Fin 4 → ℝ) → κ → Fin 2 → ℝ) (σs σt : κ → ℝ) :
    LOData (κ → Fin 4 → ℝ) where
  Dz v := G.divZ v (Tz v)
  Dx v := G.divX v (Tx v)
  σs v := fun k i => σs k * v k i
  σt v := fun k i => σt k * v k i

/-- **The linear invariant of the fully discrete LO scheme**, arXiv 2011.06072, Eqs. (24), (32),
Eqs. 12, 16, 24: for the BLD operators on a periodic mesh in a purely scattering medium
(`σ_s = σ_t`, as in the plane source and the line source problems) without source, the total mass is
exactly conserved by the forward Euler LO update, for arbitrary closures. -/
theorem lo_mass_conserved {Tz Tx : (κ → Fin 4 → ℝ) → κ → Fin 2 → ℝ} {σ : κ → ℝ} {Δt : ℝ}
    (hΔt : Δt ≠ 0) {R : Moments (κ → Fin 4 → ℝ) → (κ → Fin 4 → ℝ) × (κ → Fin 4 → ℝ)}
    {u : ℕ → Moments (κ → Fin 4 → ℝ)} {γ : ℕ → (κ → Fin 4 → ℝ) × (κ → Fin 4 → ℝ)}
    (h : ∀ n, (G.loData Tz Tx σ σ).IsLOStep R 0 Δt (γ n) (u n) (u (n + 1))) (n : ℕ) :
    G.mass (u n).φ₀₀ = G.mass (u 0).φ₀₀ := by
  refine LOData.map_conserved (Q := fun _ => 0) hΔt h G.mass (fun v => G.mass_divZ _ _)
    (fun v => G.mass_divX _ _) (fun v => ?_) (fun _ => map_zero _) n
  have : (G.loData Tz Tx σ σ).σs v - (G.loData Tz Tx σ σ).σt v = 0 := sub_self _
  rw [this, map_zero]

end Grid

/-- The BLD operators are flux-free on the periodic uniform grid, a concrete instance of `Grid`
(arXiv 2011.06072, Eq. (32)). -/
example (Nx Nz : ℕ) [NeZero Nx] [NeZero Nz] (hx hz : ℝ) (hhx : hx ≠ 0) (hhz : hz ≠ 0)
    (f : ZMod Nx × ZMod Nz → Fin 4 → ℝ) (T : ZMod Nx × ZMod Nz → Fin 2 → ℝ) :
    (periodicGrid Nx Nz hx hz hhx hhz).mass ((periodicGrid Nx Nz hx hz hhx hhz).divX f T) = 0 :=
  Grid.mass_divX _ f T

/-! ### The conservation fix, Eq. (25), and Algorithm 2 -/

section Fix

open scoped LeanDLRA.Frobenius

variable {ι A : Type*} {r : ℕ}

/-- The high-order moments `(φ₀⁰, φ₁⁰, φ₁¹)` of the full coefficient matrix `Y`, whose row `i` holds
the `P_N` moments at the spatial degree of freedom `i` and whose column `a` belongs to one spherical
harmonic. `m 0`, `m 1`, `m 2` are the columns of `Y₀⁰`, `Y₁⁰`, `Y₁¹`. -/
def momentsOf (m : Fin 3 → A) (Y : Matrix ι A ℝ) : Moments (ι → ℝ) where
  φ₀₀ := fun i => Y i (m 0)
  φ₁₀ := fun i => Y i (m 1)
  φ₁₁ := fun i => Y i (m 2)

/-- The moments as an `ι × 3` matrix, the columns of Eq. (25). -/
def Moments.toMatrix (u : Moments (ι → ℝ)) : Matrix ι (Fin 3) ℝ :=
  Matrix.of fun i => ![u.φ₀₀ i, u.φ₁₀ i, u.φ₁₁ i]

/-- The `r × 3` moment matrix of arXiv 2011.06072, Eq. (25): its row `j` is
`(v_{j00}, v_{j10}, v_{j11})`, where `V` holds the coefficients of the angular basis `W_j = Yᵀ V_j`
of Eq. (17). -/
def momentMatrix (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ) : Matrix (Fin r) (Fin 3) ℝ :=
  Matrix.of fun j a => V (m a) j

/-- The moments are determined by their matrix (arXiv 2011.06072, Eq. (25)). -/
theorem Moments.toMatrix_injective : Function.Injective (Moments.toMatrix (ι := ι)) := by
  intro u v h
  refine Moments.ext ?_ ?_ ?_ <;> funext i
  · exact congrFun (congrFun h i) 0
  · exact congrFun (congrFun h i) 1
  · exact congrFun (congrFun h i) 2

/-- Every `ι × 3` matrix is a moment matrix (arXiv 2011.06072, Eq. (25)). -/
theorem Moments.toMatrix_surjective : Function.Surjective (Moments.toMatrix (ι := ι)) := by
  intro T
  refine ⟨⟨fun i => T i 0, fun i => T i 1, fun i => T i 2⟩, ?_⟩
  ext i a
  fin_cases a <;> rfl

/-- The moment formula of arXiv 2011.06072, Sec. 3.2 and Eq. (25): the moments of `Y = K Vᵀ` are
`K` times the moment matrix. -/
theorem toMatrix_momentsOf (m : Fin 3 → A) (K : Matrix ι (Fin r) ℝ) (V : Matrix A (Fin r) ℝ) :
    (momentsOf m (K * Vᵀ)).toMatrix = K * momentMatrix m V := by
  ext i a
  fin_cases a <;> simp [Moments.toMatrix, momentsOf, momentMatrix, Matrix.mul_apply]

/-- The residual of the linear matrix equation (25) of arXiv 2011.06072, for the new `K' = K^new`,
with `W` (that is `V`) fixed, from the high-order `K` to the low-order moments `lo`. -/
def fixResidual (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ) (K K' : Matrix ι (Fin r) ℝ)
    (lo : Moments (ι → ℝ)) : Matrix ι (Fin 3) ℝ :=
  (K' - K) * momentMatrix m V - (lo.toMatrix - (momentsOf m (K * Vᵀ)).toMatrix)

/-- `K'` solves the linear matrix equation (25) of arXiv 2011.06072 exactly. -/
def IsMomentFix (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ) (K K' : Matrix ι (Fin r) ℝ)
    (lo : Moments (ι → ℝ)) : Prop :=
  fixResidual m V K K' lo = 0

/-- `K'` is a least-squares solution of the matrix equation (25) of arXiv 2011.06072 (in the
Frobenius norm): this is how the paper computes `K^new`. -/
def IsLeastSquaresFix [Fintype ι] (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ)
    (K K' : Matrix ι (Fin r) ℝ) (lo : Moments (ι → ℝ)) : Prop :=
  ∀ K'' : Matrix ι (Fin r) ℝ, ‖fixResidual m V K K' lo‖ ≤ ‖fixResidual m V K K'' lo‖

variable {m : Fin 3 → A} {V : Matrix A (Fin r) ℝ} {K K' : Matrix ι (Fin r) ℝ}
  {lo : Moments (ι → ℝ)}

/-- The residual of Eq. (25) of arXiv 2011.06072 is that of `K' B = lo`. -/
theorem fixResidual_eq (K' : Matrix ι (Fin r) ℝ) :
    fixResidual m V K K' lo = K' * momentMatrix m V - lo.toMatrix := by
  rw [fixResidual, toMatrix_momentsOf, Matrix.sub_mul]; abel

/-- **The fix makes the HO moments equal to the LO ones** (arXiv 2011.06072, Eq. (25)): `K'` solves
(25) iff the new high-order state `K' Vᵀ` has exactly the moments `lo`. -/
theorem isMomentFix_iff : IsMomentFix m V K K' lo ↔ momentsOf m (K' * Vᵀ) = lo := by
  rw [IsMomentFix, fixResidual_eq, sub_eq_zero, ← toMatrix_momentsOf]
  exact Moments.toMatrix_injective.eq_iff

/-- A least-squares solution of (25) exists for all data (arXiv 2011.06072, Sec. 3.3, whatever the
rank of the moment matrix). -/
theorem exists_isLeastSquaresFix [Fintype ι] (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ)
    (K : Matrix ι (Fin r) ℝ) (lo : Moments (ι → ℝ)) : ∃ K', IsLeastSquaresFix m V K K' lo := by
  let S : Submodule ℝ (Matrix ι (Fin 3) ℝ) :=
    LinearMap.range (Frobenius.rightMulCLM (momentMatrix m V) :
      Matrix ι (Fin r) ℝ →L[ℝ] Matrix ι (Fin 3) ℝ).toLinearMap
  obtain ⟨v, hv, hmin⟩ := S.exists_norm_eq_iInf_of_complete_subspace
    (Submodule.complete_of_finiteDimensional S) lo.toMatrix
  obtain ⟨K', rfl⟩ := hv
  refine ⟨K', fun K'' => ?_⟩
  rw [fixResidual_eq, fixResidual_eq, norm_sub_rev, norm_sub_rev (K'' * _)]
  have hK' : (Frobenius.rightMulCLM (momentMatrix m V) :
      Matrix ι (Fin r) ℝ →L[ℝ] Matrix ι (Fin 3) ℝ).toLinearMap K' = K' * momentMatrix m V := rfl
  rw [hK'] at hmin
  rw [hmin]
  exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    (⟨K'' * momentMatrix m V, K'', rfl⟩ : (S : Set (Matrix ι (Fin 3) ℝ)))

/-- arXiv 2011.06072, Eq. (25): a least-squares solution of (25) is exact as soon as any exact
solution exists. -/
theorem IsLeastSquaresFix.isMomentFix [Fintype ι] (h : IsLeastSquaresFix m V K K' lo)
    {K'' : Matrix ι (Fin r) ℝ} (hK'' : IsMomentFix m V K K'' lo) : IsMomentFix m V K K' lo := by
  have := h K''
  rw [hK'', norm_zero] at this
  exact norm_le_zero_iff.1 this

/-- **When (25) is solvable for given data**, arXiv 2011.06072, Eq. (25) (the paper only says that
least squares is used): iff every row of the moment defect `lo - moments(K Vᵀ)` lies in the row
space of the moment matrix. -/
theorem exists_isMomentFix_iff :
    (∃ K', IsMomentFix m V K K' lo) ↔ ∀ i, ∃ x : Fin r → ℝ, x ᵥ* momentMatrix m V =
      fun a => (lo.toMatrix - (momentsOf m (K * Vᵀ)).toMatrix) i a := by
  simp only [IsMomentFix, fixResidual, sub_eq_zero]
  constructor
  · rintro ⟨K', h⟩ i
    refine ⟨(K' - K) i, ?_⟩
    funext a
    rw [← h]
    rfl
  · intro h
    choose x hx using h
    refine ⟨K + Matrix.of x, ?_⟩
    rw [add_sub_cancel_left]
    ext i a
    exact congrFun (hx i) a

/-- **The rank condition of Eq. (25)**: (25) is solvable for *every* target iff the `r × 3` moment
matrix has rank 3 (`ι` nonempty). This is `holo_correction_solvable_iff` of the library
(`OpenProblems/Conservation/Part3c.lean`, there the only content of OP-CO-30), in the notation of
this file. For a *fixed* target rank 3 is not necessary: see `exact_without_rank_three`. -/
theorem forall_exists_isMomentFix_iff [Nonempty ι] (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ)
    (K : Matrix ι (Fin r) ℝ) :
    (∀ lo : Moments (ι → ℝ), ∃ K', IsMomentFix m V K K' lo) ↔ (momentMatrix m V).rank = 3 := by
  rw [← OpenProblems.Conservation.holo_correction_solvable_iff K (momentMatrix m V)]
  constructor
  · intro h T
    obtain ⟨lo, rfl⟩ := Moments.toMatrix_surjective T
    obtain ⟨K', hK'⟩ := h lo
    refine ⟨K' - K, ?_⟩
    rw [add_sub_cancel]
    rw [IsMomentFix, fixResidual_eq, sub_eq_zero] at hK'
    exact hK'
  · intro h lo
    obtain ⟨dK, hdK⟩ := h lo.toMatrix
    refine ⟨K + dK, ?_⟩
    rw [IsMomentFix, fixResidual_eq, sub_eq_zero]
    exact hdK

/-- **The claim "the match is exact iff the moment matrix has rank 3" fails for fixed data**
(arXiv 2011.06072, Eq. (25); the paper itself only speaks of least squares). Here `r = 1`, the
angular basis is `Y₀⁰` and the rank is `1`, the HO moments `(0, 0, 0)` differ from the LO moments
`(1, 0, 0)`, and (25) is solved exactly. Such data, with defect in `φ₀⁰` only, is what Algorithm 2
produces, see `IsHOLOStep.moments_eq`. -/
theorem exact_without_rank_three :
    ∃ (V : Matrix (Fin 3) (Fin 1) ℝ) (K K' : Matrix (Fin 1) (Fin 1) ℝ) (lo : Moments (Fin 1 → ℝ)),
      momentsOf id (K * Vᵀ) ≠ lo ∧ IsMomentFix id V K K' lo ∧ (momentMatrix id V).rank ≠ 3 := by
  refine ⟨Matrix.of fun a _ => if a = 0 then 1 else 0, 0, 1, ⟨1, 0, 0⟩, ?_, ?_, ?_⟩
  · intro h
    have := congrFun (congrArg Moments.φ₀₀ h) 0
    simp [momentsOf] at this
  · rw [isMomentFix_iff]
    refine Moments.ext ?_ ?_ ?_ <;> funext i <;> fin_cases i <;>
      simp [momentsOf, Matrix.mul_apply]
  · have := (momentMatrix (id : Fin 3 → Fin 3)
      (Matrix.of fun a _ => if a = 0 then 1 else 0 : Matrix (Fin 3) (Fin 1) ℝ)).rank_le_height
    omega

/-- arXiv 2011.06072, Eq. (25), "preserving the low-rank representation": the corrected state has
rank at most `r`. -/
theorem rank_fix_le [Fintype A] (K' : Matrix ι (Fin r) ℝ) (V : Matrix A (Fin r) ℝ) :
    (K' * Vᵀ).rank ≤ r :=
  (Matrix.rank_mul_le_left _ _).trans (by simpa using K'.rank_le_card_width)

/-- arXiv 2011.06072, Sec. 3.3, "where we keep `W_j` unchanged": for orthonormal `V`, the corrected
state lies in the range of the fixed right projector `Q₀ = V Vᵀ`, and so does the correction. -/
theorem rightProj_fix [Fintype ι] [Fintype A] (hV : Vᵀ * V = 1) (K K' : Matrix ι (Fin r) ℝ) :
    rightProj V (K' * Vᵀ) = K' * Vᵀ ∧
      rightProj V (K' * Vᵀ - K * Vᵀ) = K' * Vᵀ - K * Vᵀ := by
  have : ∀ X : Matrix ι (Fin r) ℝ, rightProj V (X * Vᵀ) = X * Vᵀ := fun X =>
    (rightProj_eq_self_iff hV _).2 ⟨X, rfl⟩
  exact ⟨this K', by rw [← Matrix.sub_mul, this]⟩

/-- The minimal-norm solution of (25), `K^new = K + D (Bᵀ B)⁻¹ Bᵀ` for the defect
`D = lo - K B` and the moment matrix `B`. -/
noncomputable def minNormFix (m : Fin 3 → A) (V : Matrix A (Fin r) ℝ) (K : Matrix ι (Fin r) ℝ)
    (lo : Moments (ι → ℝ)) : Matrix ι (Fin r) ℝ :=
  K + (lo.toMatrix - K * momentMatrix m V) * ((momentMatrix m V)ᵀ * momentMatrix m V)⁻¹ *
    (momentMatrix m V)ᵀ

private theorem isUnit_det_of_rank (B : Matrix (Fin r) (Fin 3) ℝ) (hB : B.rank = 3) :
    IsUnit (Bᵀ * B).det := by
  have h : (Bᵀ * B).rank = Fintype.card (Fin 3) := by
    rw [Matrix.rank_transpose_mul_self, hB, Fintype.card_fin]
  have := Matrix.mulVec_surjective_iff_isUnit.1 (Matrix.mulVec_surjective_iff_rank_eq_card.2 h)
  exact (Matrix.isUnit_iff_isUnit_det _).1 this

/-- **The least-squares update of Eq. (25) for rank 3** (arXiv 2011.06072, Eq. (25); from
`holo_correction_min_norm` of the library): for rank 3, `minNormFix` is an exact solution, every
least-squares solution is exact, and among all solutions it changes `K`, and for orthonormal `V`
also the state `K Vᵀ`, the least. -/
theorem minNormFix_spec [Fintype ι] [Fintype A] (hB : (momentMatrix m V).rank = 3) :
    IsMomentFix m V K (minNormFix m V K lo) lo ∧
      (∀ K', IsLeastSquaresFix m V K K' lo → IsMomentFix m V K K' lo) ∧
      (∀ K', IsMomentFix m V K K' lo → ‖minNormFix m V K lo - K‖ ≤ ‖K' - K‖) ∧
      (Vᵀ * V = 1 → ∀ K', IsMomentFix m V K K' lo →
        ‖minNormFix m V K lo * Vᵀ - K * Vᵀ‖ ≤ ‖K' * Vᵀ - K * Vᵀ‖) := by
  obtain ⟨h₁, h₂, -⟩ := OpenProblems.Conservation.holo_correction_min_norm K (momentMatrix m V)
    (isUnit_det_of_rank _ hB) lo.toMatrix
  have hfix : IsMomentFix m V K (minNormFix m V K lo) lo := by
    rw [IsMomentFix, fixResidual_eq, sub_eq_zero]
    exact h₁
  have hmin : ∀ K', IsMomentFix m V K K' lo → ‖minNormFix m V K lo - K‖ ≤ ‖K' - K‖ := by
    intro K' hK'
    rw [IsMomentFix, fixResidual_eq, sub_eq_zero] at hK'
    have := h₂ (K' - K) (by rw [add_sub_cancel]; exact hK')
    rwa [minNormFix, add_sub_cancel_left]
  refine ⟨hfix, fun K' hK' => hK'.isMomentFix hfix, hmin, fun hV K' hK' => ?_⟩
  rw [← Matrix.sub_mul, ← Matrix.sub_mul, Frobenius.norm_mul_transpose_of_orthonormal hV,
    Frobenius.norm_mul_transpose_of_orthonormal hV]
  exact hmin K' hK'

/-- The non-vacuity of the rank condition of arXiv 2011.06072, Eq. (25) (not in the paper; this is
the setting `Q₀ C = C` of the conservative truncation of the library): if `Q₀ = V Vᵀ` fixes the
three moment directions and `m` is injective, the moment matrix has rank 3, with orthonormal
columns. -/
theorem rank_momentMatrix_of_contains [Fintype A] [DecidableEq A] (hm : Function.Injective m)
    (hV : ∀ a, (V * Vᵀ) *ᵥ Pi.single (m a) 1 = Pi.single (m a) 1) :
    (momentMatrix m V)ᵀ * momentMatrix m V = 1 ∧ (momentMatrix m V).rank = 3 := by
  have hB : (momentMatrix m V)ᵀ * momentMatrix m V = 1 := by
    ext a b
    have h := congrFun (hV b) (m a)
    rw [Matrix.mulVec_single_one] at h
    have e : ((momentMatrix m V)ᵀ * momentMatrix m V) a b = (V * Vᵀ) (m a) (m b) := by
      simp [Matrix.mul_apply, momentMatrix]
    rw [e]
    have h' : (V * Vᵀ) (m a) (m b) = (Pi.single (m b) 1 : A → ℝ) (m a) := h
    rw [h', Pi.single_apply, Matrix.one_apply]
    simp [hm.eq_iff]
  refine ⟨hB, ?_⟩
  rw [← Matrix.rank_transpose_mul_self, hB, Matrix.rank_one, Fintype.card_fin]

/-- The full basis contains all moment directions: the condition of
`rank_momentMatrix_of_contains` can hold (arXiv 2011.06072, full rank `r = n`). -/
example (m : Fin 3 → Fin 5) (hm : Function.Injective m) :
    (momentMatrix m (1 : Matrix (Fin 5) (Fin 5) ℝ)).rank = 3 :=
  (rank_momentMatrix_of_contains hm fun a => by
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.one_mulVec]).2

/-- The `n × 3` matrix of the three moment directions: `Y E` holds the three moment columns of `Y`,
and right multiplication by `E Eᵀ` is the projector `C` of `Stability/Conservation.lean`. -/
def momentBasis [DecidableEq A] (m : Fin 3 → A) : Matrix A (Fin 3) ℝ :=
  Matrix.of fun a b => if a = m b then 1 else 0

/-- **The fix (25) compared with the conservative truncation** (arXiv 2011.06072, Eq. (25); slice
note, `consTrunc` of `Stability/Conservation.lean`). If the fixed basis contains the three moment
directions, the minimal-norm fix is the conservative truncation with the conserved directions `E`:
the moments come from the LO solution, and the part of the HO state orthogonal to them is kept.
(In the conservative truncation the basis changes; here it does not, so this needs the moment
directions in the basis, while (25) in general does not.) -/
theorem fix_eq_consTrunc [Fintype ι] [Fintype A] [DecidableEq A] (hm : Function.Injective m)
    (hV : ∀ a, (V * Vᵀ) *ᵥ Pi.single (m a) 1 = Pi.single (m a) 1) (K : Matrix ι (Fin r) ℝ)
    (lo : Moments (ι → ℝ)) :
    minNormFix m V K lo * Vᵀ =
        consTrunc (rightProj (momentBasis m))
          (fun _ => K * Vᵀ - rightProj (momentBasis m) (K * Vᵀ))
          (lo.toMatrix * (momentBasis m)ᵀ) ∧
      rightProj (momentBasis m) (minNormFix m V K lo * Vᵀ) = lo.toMatrix * (momentBasis m)ᵀ := by
  have hE : (momentBasis m)ᵀ * momentBasis m = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, momentBasis, Matrix.of_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply, hm.eq_iff]
    exact if_congr eq_comm rfl rfl
  have hBE : Vᵀ * momentBasis m = momentMatrix m V := by
    ext j b
    simp [Matrix.mul_apply, momentBasis, momentMatrix]
  have hVB : V * momentMatrix m V = momentBasis m := by
    ext a b
    have h := congrFun (hV b) a
    rw [Matrix.mulVec_single_one] at h
    have e : (V * momentMatrix m V) a b = (V * Vᵀ) a (m b) := by
      simp [Matrix.mul_apply, momentMatrix]
    have h' : (V * Vᵀ) a (m b) = (Pi.single (m b) 1 : A → ℝ) a := h
    rw [e, h', Pi.single_apply]
    rfl
  have hBB := (rank_momentMatrix_of_contains hm hV).1
  have hfix : minNormFix m V K lo * Vᵀ =
      K * Vᵀ + (lo.toMatrix - K * momentMatrix m V) * (momentBasis m)ᵀ := by
    rw [minNormFix, hBB, inv_one, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc _ _ Vᵀ,
      ← Matrix.transpose_mul, hVB]
  have hC : ∀ X : Matrix ι A ℝ,
      rightProj (momentBasis m) X = X * (momentBasis m * (momentBasis m)ᵀ) := fun _ => rfl
  have hT : rightProj (momentBasis m) (lo.toMatrix * (momentBasis m)ᵀ) =
      lo.toMatrix * (momentBasis m)ᵀ := by
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc (momentBasis m)ᵀ, hE, Matrix.one_mul]
  have hY : rightProj (momentBasis m) (K * Vᵀ) = K * momentMatrix m V * (momentBasis m)ᵀ := by
    rw [hC, ← Matrix.mul_assoc, Matrix.mul_assoc K, hBE]
  have hOrth := isOrthProj_rightProj (m := ι) hE
  have first : minNormFix m V K lo * Vᵀ =
      consTrunc (rightProj (momentBasis m))
        (fun _ => K * Vᵀ - rightProj (momentBasis m) (K * Vᵀ))
        (lo.toMatrix * (momentBasis m)ᵀ) := by
    simp only [consTrunc]
    rw [hT, hY, hfix, Matrix.sub_mul]
    abel
  refine ⟨first, ?_⟩
  rw [first, consTrunc_moments hOrth ?_, hT]
  change rightProj (momentBasis m) (K * Vᵀ - rightProj (momentBasis m) (K * Vᵀ)) = 0
  rw [map_sub, hOrth.idem, sub_self]

/-- The vector `(1, 0, 0)`: a defect in `φ₀⁰` only. -/
def e₀ : Fin 3 → ℝ := ![1, 0, 0]

/-- arXiv 2011.06072, Eq. (25) for the data of Algorithm 2 (not in the paper): if the high-order
and low-order first moments agree, (25) is solvable if `(1, 0, 0)` lies in the row space of the
moment matrix. -/
theorem exists_isMomentFix_of_e₀ (he : ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m V = e₀)
    (h₁ : lo.φ₁₀ = (momentsOf m (K * Vᵀ)).φ₁₀) (h₂ : lo.φ₁₁ = (momentsOf m (K * Vᵀ)).φ₁₁) :
    ∃ K', IsMomentFix m V K K' lo := by
  obtain ⟨w, hw⟩ := he
  rw [exists_isMomentFix_iff]
  intro i
  refine ⟨(lo.φ₀₀ i - (momentsOf m (K * Vᵀ)).φ₀₀ i) • w, ?_⟩
  rw [Matrix.smul_vecMul, hw]
  funext a
  fin_cases a <;> simp [e₀, Moments.toMatrix, h₁, h₂]

/-- arXiv 2011.06072, Eq. (25) for the data of Algorithm 2 (not in the paper): the converse of
`exists_isMomentFix_of_e₀` if the defect in `φ₀⁰` does not vanish identically. So rank 3 is more
than Algorithm 2 needs. -/
theorem e₀_mem_of_exists_isMomentFix {i : ι} (hi : lo.φ₀₀ i ≠ (momentsOf m (K * Vᵀ)).φ₀₀ i)
    (h₁ : lo.φ₁₀ = (momentsOf m (K * Vᵀ)).φ₁₀) (h₂ : lo.φ₁₁ = (momentsOf m (K * Vᵀ)).φ₁₁)
    (h : ∃ K', IsMomentFix m V K K' lo) : ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m V = e₀ := by
  obtain ⟨x, hx⟩ := exists_isMomentFix_iff.1 h i
  refine ⟨(lo.φ₀₀ i - (momentsOf m (K * Vᵀ)).φ₀₀ i)⁻¹ • x, ?_⟩
  have hne := sub_ne_zero.2 hi
  rw [Matrix.smul_vecMul, hx]
  funext a
  fin_cases a <;> simp [e₀, Moments.toMatrix, h₁, h₂, hne]

/-- Rank 3 implies the weaker condition of `exists_isMomentFix_of_e₀` (arXiv 2011.06072,
Eq. (25)). -/
theorem exists_vecMul_eq_e₀ (hB : (momentMatrix m V).rank = 3) :
    ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m V = e₀ :=
  (Matrix.vecMul_surjective_iff_rank_eq_card.2 (by simpa using hB)) e₀

/-- **One step of the HOLO algorithm**, arXiv 2011.06072, Algorithm 2, from the state `Y` with
LO moments `lo` at `tₙ` to `Knew Vpᵀ` with LO moments `lo'` at `tₙ₊₁`. The DLR step of Algorithm 1
produces the prediction `Kp Vpᵀ` from `Y`. It is arbitrary here, so nothing about Algorithm 1 is
used. `lo'` is the LO update (24) with the closure (23) computed from `Y` and the prediction, and
`Knew` is a least-squares solution of (25) with `Vp` fixed. The removal terms `R` are
`L.printedRemoval` for the printed formulas. -/
structure IsHOLOStep [Fintype ι] (L : LOData (ι → ℝ)) (R : Moments (ι → ℝ) → (ι → ℝ) × (ι → ℝ))
    (Q : ι → ℝ) (Δt : ℝ) (m : Fin 3 → A) (Y : Matrix ι A ℝ) (lo : Moments (ι → ℝ))
    (Kp : Matrix ι (Fin r) ℝ) (Vp : Matrix A (Fin r) ℝ) (Knew : Matrix ι (Fin r) ℝ)
    (lo' : Moments (ι → ℝ)) : Prop where
  lo_step : L.IsLOStep R Q Δt (L.closure R Δt (momentsOf m Y) (momentsOf m (Kp * Vpᵀ))) lo lo'
  fix : IsLeastSquaresFix m Vp Kp Knew lo'

/-- arXiv 2011.06072, Algorithm 2 is well defined: for `Δt ≠ 0` and all data and DLR predictions, a
step exists. So all hypotheses of `holo_conservative` below can be met, except possibly its rank
condition (see `rank_momentMatrix_of_contains`). -/
theorem exists_isHOLOStep [Fintype ι] (L : LOData (ι → ℝ)) (R : Moments (ι → ℝ) → (ι → ℝ) × (ι → ℝ))
    (Q : ι → ℝ) {Δt : ℝ} (hΔt : Δt ≠ 0) (m : Fin 3 → A) (Y : Matrix ι A ℝ) (lo : Moments (ι → ℝ))
    (Kp : Matrix ι (Fin r) ℝ) (Vp : Matrix A (Fin r) ℝ) :
    ∃ Knew lo', IsHOLOStep L R Q Δt m Y lo Kp Vp Knew lo' := by
  obtain ⟨Knew, h⟩ := exists_isLeastSquaresFix m Vp Kp
    (L.loStep R Q Δt (L.closure R Δt (momentsOf m Y) (momentsOf m (Kp * Vpᵀ))) lo)
  exact ⟨Knew, _, (LOData.isLOStep_iff hΔt).2 rfl, h⟩

variable {L : LOData (ι → ℝ)} {R : Moments (ι → ℝ) → (ι → ℝ) × (ι → ℝ)} {Q : ι → ℝ} {Δt : ℝ}

/-- **The fix makes one HOLO step exact**, arXiv 2011.06072, Sec. 3.3: if the moments of `Y` are the
LO moments `lo` at `tₙ`, and `(1, 0, 0)` is in the row space of the moment matrix (in particular if
it has rank 3), then the moments of the corrected state are the LO moments at `tₙ₊₁`. The point
is that by the closure (23) the DLR prediction already has the LO first moments, so that the
defect in (25) is in `φ₀⁰` only. -/
theorem IsHOLOStep.moments_eq [Fintype ι] {Y : Matrix ι A ℝ} {Kp Knew : Matrix ι (Fin r) ℝ}
    {Vp : Matrix A (Fin r) ℝ} {lo' : Moments (ι → ℝ)}
    (h : IsHOLOStep L R Q Δt m Y lo Kp Vp Knew lo') (hΔt : Δt ≠ 0)
    (hY : momentsOf m Y = lo) (he : ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m Vp = e₀) :
    momentsOf m (Knew * Vpᵀ) = lo' := by
  obtain ⟨h₁, h₂⟩ := h.lo_step.reproduces hΔt hY.symm
  obtain ⟨K'', hK''⟩ := exists_isMomentFix_of_e₀ he h₁ h₂
  exact isMomentFix_iff.1 (h.fix.isMomentFix hK'')

/-- **The HOLO algorithm follows the LO solution**, arXiv 2011.06072, Algorithm 2: if the initial
moments agree, the moments of the HOLO states `Y n` are the LO moments at all times, for arbitrary
DLR predictions. -/
theorem holo_moments_eq [Fintype ι] {Y : ℕ → Matrix ι A ℝ} {Kp Knew : ℕ → Matrix ι (Fin r) ℝ}
    {Vp : ℕ → Matrix A (Fin r) ℝ} {lo : ℕ → Moments (ι → ℝ)} {Q : ℕ → ι → ℝ} (hΔt : Δt ≠ 0)
    (h : ∀ n, IsHOLOStep L R (Q n) Δt m (Y n) (lo n) (Kp n) (Vp n) (Knew n) (lo (n + 1)))
    (hY : ∀ n, Y (n + 1) = Knew n * (Vp n)ᵀ) (h0 : momentsOf m (Y 0) = lo 0)
    (he : ∀ n, ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m (Vp n) = e₀) (n : ℕ) :
    momentsOf m (Y n) = lo n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hY]
    exact (h n).moments_eq hΔt ih (he n)

/-- **The HOLO algorithm is conservative**, the main claim of arXiv 2011.06072 (abstract, Sec. 3.3,
Algorithm 2, stated there without proof and observed in the numerics). Let the initial LO moments be
those of the initial state, let `(1, 0, 0)` lie in the row space of each moment matrix (in
particular let the moment matrices have rank 3), and let `ℓ` be a linear functional that annihilates
the discrete derivatives. Then the HOLO states `Y n` have rank at most `r` for `n ≥ 1` and satisfy
the global balance of the LO system, and if `ℓ` annihilates absorption and sources, `ℓ φ₀⁰` is
exactly conserved. The closures, the bases and the DLR predictions are arbitrary, so the
non-conservation of the DLR step does not matter. -/
theorem holo_conservative [Fintype ι] [Fintype A] {Y : ℕ → Matrix ι A ℝ}
    {Kp Knew : ℕ → Matrix ι (Fin r) ℝ} {Vp : ℕ → Matrix A (Fin r) ℝ}
    {lo : ℕ → Moments (ι → ℝ)} {Q : ℕ → ι → ℝ} (hΔt : Δt ≠ 0)
    (h : ∀ n, IsHOLOStep L R (Q n) Δt m (Y n) (lo n) (Kp n) (Vp n) (Knew n) (lo (n + 1)))
    (hY : ∀ n, Y (n + 1) = Knew n * (Vp n)ᵀ) (h0 : momentsOf m (Y 0) = lo 0)
    (he : ∀ n, ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m (Vp n) = e₀)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (hz : ∀ v, ℓ (L.Dz v) = 0) (hx : ∀ v, ℓ (L.Dx v) = 0) :
    (∀ n, (Y (n + 1)).rank ≤ r) ∧
    (∀ n, ℓ (momentsOf m (Y (n + 1))).φ₀₀ = ℓ (momentsOf m (Y n)).φ₀₀ +
      Δt * (ℓ (L.σs (momentsOf m (Y n)).φ₀₀ - L.σt (momentsOf m (Y n)).φ₀₀) +
        1 / (2 * √π) * ℓ (Q n))) ∧
    ((∀ v, ℓ (L.σs v - L.σt v) = 0) → (∀ n, ℓ (Q n) = 0) →
      ∀ n, ℓ (momentsOf m (Y n)).φ₀₀ = ℓ (momentsOf m (Y 0)).φ₀₀) := by
  have hmom := holo_moments_eq hΔt h hY h0 he
  refine ⟨fun n => by rw [hY]; exact rank_fix_le _ _, fun n => ?_, fun ha hQ n => ?_⟩
  · rw [hmom, hmom]
    exact (h n).lo_step.map_balance_of_flux_free hΔt ℓ hz hx
  · rw [hmom, hmom]
    exact LOData.map_conserved hΔt (fun n => (h n).lo_step) ℓ hz hx ha hQ n

end Fix

section HOLOGrid

variable {κ A : Type*} (G : Grid κ)

/-- The operators of `Grid.loData` on the fields `κ × Fin 4 → ℝ`, which are the columns of the
coefficient matrices `Y` of Algorithm 2: the spatial degrees of freedom are the nodes `(k, i)`. -/
noncomputable def Grid.flatData (Tz Tx : (κ → Fin 4 → ℝ) → κ → Fin 2 → ℝ) (σs σt : κ → ℝ) :
    LOData (κ × Fin 4 → ℝ) where
  Dz v := Function.uncurry (G.divZ (Function.curry v) (Tz (Function.curry v)))
  Dx v := Function.uncurry (G.divX (Function.curry v) (Tx (Function.curry v)))
  σs v := fun p => σs p.1 * v p
  σt v := fun p => σt p.1 * v p

/-- The total mass `Grid.mass` on the fields `κ × Fin 4 → ℝ`. -/
noncomputable def Grid.flatMass [Fintype κ] : (κ × Fin 4 → ℝ) →ₗ[ℝ] ℝ :=
  G.mass ∘ₗ (LinearEquiv.curry ℝ ℝ κ (Fin 4)).toLinearMap

/-- **The fully discrete HOLO algorithm conserves the total mass**, arXiv 2011.06072, Algorithm 2
with the LO scheme (24), (32) on a periodic mesh, in a purely scattering medium without source. This
is the setting of the plane source and the line source problems (Secs. 5.1, 5.3), except for the
periodic mesh. If the initial LO moments are those of the initial state and `(1, 0, 0)` is in the
row space of every moment matrix, the mass of `φ₀⁰` of the HOLO states is exactly constant and their
rank stays at most `r`, for arbitrary closures, DLR predictions and single valued numerical
traces. -/
theorem Grid.holo_mass_conserved [Fintype κ] [Fintype A] {r : ℕ}
    {Tz Tx : (κ → Fin 4 → ℝ) → κ → Fin 2 → ℝ} {σ : κ → ℝ} {Δt : ℝ} (hΔt : Δt ≠ 0)
    {R : Moments (κ × Fin 4 → ℝ) → (κ × Fin 4 → ℝ) × (κ × Fin 4 → ℝ)} {m : Fin 3 → A}
    {Y : ℕ → Matrix (κ × Fin 4) A ℝ} {Kp Knew : ℕ → Matrix (κ × Fin 4) (Fin r) ℝ}
    {Vp : ℕ → Matrix A (Fin r) ℝ} {lo : ℕ → Moments (κ × Fin 4 → ℝ)}
    (h : ∀ n, IsHOLOStep (G.flatData Tz Tx σ σ) R 0 Δt m (Y n) (lo n) (Kp n) (Vp n) (Knew n)
      (lo (n + 1)))
    (hY : ∀ n, Y (n + 1) = Knew n * (Vp n)ᵀ) (h0 : momentsOf m (Y 0) = lo 0)
    (he : ∀ n, ∃ w : Fin r → ℝ, w ᵥ* momentMatrix m (Vp n) = e₀) (n : ℕ) :
    (Y (n + 1)).rank ≤ r ∧
      G.flatMass (momentsOf m (Y n)).φ₀₀ = G.flatMass (momentsOf m (Y 0)).φ₀₀ := by
  obtain ⟨h₁, -, h₃⟩ := holo_conservative (Q := fun _ => 0) hΔt h hY h0 he G.flatMass
    (fun v => G.mass_divZ _ _) (fun v => G.mass_divX _ _)
  refine ⟨h₁ n, h₃ (fun v => ?_) (fun _ => map_zero _) n⟩
  have : (G.flatData Tz Tx σ σ).σs v - (G.flatData Tz Tx σ σ).σt v = 0 := sub_self _
  rw [this, map_zero]

end HOLOGrid

/-! ### The continuous system, Eqs. (12), (16) -/

section PDE

variable {n : ℕ}

/-- Points of the space `ℝⁿ⁺¹`: `n = 0`, `1`, `2` are the slab, the `xz`-geometry of the paper's
numerics, and the full geometry of Eq. (1). -/
abbrev Pt (n : ℕ) : Type := Fin (n + 1) → ℝ

/-- The divergence `∇ · F`. -/
noncomputable def divergence (F : Pt n → Pt n) (r : Pt n) : ℝ :=
  ∑ i, fderiv ℝ F r (Pi.single i 1) i

/-- The net outflow of `F` through the boundary of the box `[a, b]`, face by face. -/
noncomputable def netOutflow (a b : Pt n) (F : Pt n → Pt n) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) x) i) -
      ∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) x) i)

/-- Boundary conditions for arXiv 2011.06072, Eqs. 12, 16, 24: there is no net outflow if the normal
component of `F` agrees on opposite faces, that is for periodic boundary conditions or a vanishing
normal component. -/
theorem netOutflow_eq_zero {a b : Pt n} {F : Pt n → Pt n}
    (h : ∀ i, ∀ x ∈ Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F (i.insertNth (b i) x) i = F (i.insertNth (a i) x) i) :
    netOutflow a b F = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sub_eq_zero]
  exact setIntegral_congr_fun measurableSet_Icc (h i)

/-- The divergence of a `C¹` field is continuous (for arXiv 2011.06072, Eqs. 12, 16, 24). -/
theorem continuous_divergence {F : Pt n → Pt n} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  have hd : ∀ i : Fin (n + 1), Continuous fun r => fderiv ℝ F r (Pi.single i 1) i := fun i =>
    (continuous_apply i).comp ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  unfold divergence
  fun_prop

/-- The divergence theorem on a box, the "conservative form" of arXiv 2011.06072, Eq. (12), from
Mathlib. -/
theorem integral_divergence {a b : Pt n} (hab : a ≤ b) {F : Pt n → Pt n} (hF : ContDiff ℝ 1 F) :
    ∫ r in Set.Icc a b, divergence F r = netOutflow a b F :=
  integral_divergence_of_hasFDerivAt_off_countable a b hab F (fderiv ℝ F) ∅ Set.countable_empty
    hF.continuous.continuousOn (fun x _ => (hF.differentiable one_ne_zero x).hasFDerivAt)
    ((continuous_divergence hF).continuousOn.integrableOn_compact isCompact_Icc)

/-- The time derivative of a jointly `C¹` field, as a jointly continuous function. -/
private theorem time_deriv {φ : ℝ → Pt n → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Pt n => φ p.1 p.2)) :
    ∃ g : ℝ × Pt n → ℝ, Continuous g ∧ ∀ s r, HasDerivAt (fun s => φ s r) (g (s, r)) s := by
  refine ⟨fun p => fderiv ℝ (fun p : ℝ × Pt n => φ p.1 p.2) p (1, 0),
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const, fun s r => ?_⟩
  have h1 : HasFDerivAt (fun p : ℝ × Pt n => φ p.1 p.2)
      (fderiv ℝ (fun p : ℝ × Pt n => φ p.1 p.2) (s, r)) (s, r) :=
    (hφ.differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (s, r)) ((1 : ℝ), (0 : Pt n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s r)
  exact h1.comp_hasDerivAt s h2

/-- Differentiation under the integral sign on a box, for a jointly `C¹` field (for arXiv
2011.06072, Eqs. 12, 16, 24). -/
theorem hasDerivAt_integral_box {a b : Pt n} {φ : ℝ → Pt n → ℝ}
    (hφ : ContDiff ℝ 1 (fun p : ℝ × Pt n => φ p.1 p.2)) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in Set.Icc a b, φ s r)
      (∫ r in Set.Icc a b, deriv (fun s => φ s r) t) t := by
  obtain ⟨g, hg, hd⟩ := time_deriv hφ
  have hcomp : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hg.continuousOn
  have hcont : ∀ s, Continuous (φ s) := fun s =>
    hφ.continuous.comp (continuous_const.prodMk continuous_id)
  have hgs : Continuous fun r => g (t, r) := hg.comp (continuous_const.prodMk continuous_id)
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by simpa using isCompact_Icc.measure_lt_top⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b)) (F := fun s r => φ s r) (F' := fun s r => g (s, r))
    (x₀ := t) (s := Set.Icc (t - 1) (t + 1)) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    ((hcont t).continuousOn.integrableOn_compact isCompact_Icc)
    hgs.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr s hs =>
      hM (s, r) ⟨hs, hr⟩))
    (integrable_const M)
    (Eventually.of_forall fun r s _ => hd s r)
  have e : (∫ r in Set.Icc a b, deriv (fun s => φ s r) t) = ∫ r in Set.Icc a b, g (t, r) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
    exact (hd t r).deriv
  rw [e]
  exact key.2

/-- **The low-order system of arXiv 2011.06072, Eqs. (12), (16)**, on the box `[a, b]` and for the
times in `I`, with particle speed `c`, cross-sections `σs`, `σt`, source `Q` and closure `γ` (the
fields `φ`, `J` are `C¹` in `(t, r)` on the whole space, which is a mild restriction by Whitney's
extension theorem). -/
structure IsLOSolution (c : ℝ) (a b : Pt n) (I : Set ℝ) (σs σt : Pt n → ℝ) (Q : ℝ → Pt n → ℝ)
    (φ : ℝ → Pt n → ℝ) (J γ : ℝ → Pt n → Pt n) : Prop where
  φ_smooth : ContDiff ℝ 1 (fun p : ℝ × Pt n => φ p.1 p.2)
  J_smooth : ContDiff ℝ 1 (fun p : ℝ × Pt n => J p.1 p.2)
  eq12 : ∀ t ∈ I, ∀ r ∈ Set.Icc a b,
    1 / c * deriv (fun s => φ s r) t + divergence (J t) r + σt r * φ t r =
      σs r * φ t r + Q t r
  eq16 : ∀ t ∈ I, ∀ r ∈ Set.Icc a b, ∀ i,
    1 / c * deriv (fun s => J s r i) t + 1 / 3 * fderiv ℝ (φ t) r (Pi.single i 1) +
      σt r * J t r i = γ t r i

variable {c : ℝ} {a b : Pt n} {I : Set ℝ} {σs σt : Pt n → ℝ} {Q : ℝ → Pt n → ℝ}
  {φ : ℝ → Pt n → ℝ} {J γ : ℝ → Pt n → Pt n}

/-- **The LO system is conservative in `φ` for every closure `γ`**, arXiv 2011.06072, Eqs. (12),
(16) ("the solution is conservative in `φ` regardless of the value of the closure term because `J`
appears in conservative form"). The total number of particles `∫ φ` on a box in any dimension
changes only through the net outflow of `J`, absorption and sources. -/
theorem IsLOSolution.hasDerivAt_total (h : IsLOSolution c a b I σs σt Q φ J γ) (hc : c ≠ 0)
    (hab : a ≤ b) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => ∫ r in Set.Icc a b, φ s r)
      (c * ((∫ r in Set.Icc a b, ((σs r - σt r) * φ t r + Q t r)) - netOutflow a b (J t))) t := by
  have hJ : ContDiff ℝ 1 (J t) := h.J_smooth.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨g, hg, hd⟩ := time_deriv h.φ_smooth
  have hgs : Continuous fun r => g (t, r) := hg.comp (continuous_const.prodMk continuous_id)
  have hdiv := continuous_divergence hJ
  have hbox : ∀ {f : Pt n → ℝ}, Continuous f → IntegrableOn f (Set.Icc a b) := fun hf =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have e₁ : (∫ r in Set.Icc a b, deriv (fun s => φ s r) t) = ∫ r in Set.Icc a b, g (t, r) :=
    setIntegral_congr_fun measurableSet_Icc fun r _ => (hd t r).deriv
  have e₂ : (∫ r in Set.Icc a b, ((σs r - σt r) * φ t r + Q t r)) =
      ∫ r in Set.Icc a b, (1 / c * g (t, r) + divergence (J t) r) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have := h.eq12 t ht r hr
    rw [(hd t r).deriv] at this
    linarith
  have e₃ : (∫ r in Set.Icc a b, (1 / c * g (t, r) + divergence (J t) r)) =
      1 / c * (∫ r in Set.Icc a b, g (t, r)) + netOutflow a b (J t) := by
    rw [integral_add ((hbox hgs).const_mul _) (hbox hdiv), integral_const_mul,
      integral_divergence hab hJ]
  have key := hasDerivAt_integral_box (a := a) (b := b) h.φ_smooth t
  rw [e₁] at key
  convert key using 1
  rw [e₂, e₃]
  field_simp
  ring

/-- arXiv 2011.06072, Eqs. (12), (16), global conservation: without net outflow, in a purely
scattering medium and without sources, `∫ φ` is constant in time, for every closure `γ`. -/
theorem IsLOSolution.total_eq (h : IsLOSolution c a b I σs σt Q φ J γ) (hc : c ≠ 0)
    (hab : a ≤ b) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hI : Set.Icc t₀ t₁ ⊆ I)
    (hflux : ∀ t ∈ Set.Icc t₀ t₁, netOutflow a b (J t) = 0)
    (hσ : ∀ r ∈ Set.Icc a b, σs r = σt r)
    (hQ : ∀ t ∈ Set.Icc t₀ t₁, ∀ r ∈ Set.Icc a b, Q t r = 0) :
    ∫ r in Set.Icc a b, φ t₁ r = ∫ r in Set.Icc a b, φ t₀ r := by
  have hd : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt (fun s => ∫ r in Set.Icc a b, φ s r) 0 t := by
    intro t ht'
    have key := h.hasDerivAt_total hc hab (hI ht')
    have e : (∫ r in Set.Icc a b, ((σs r - σt r) * φ t r + Q t r)) = 0 := by
      rw [setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Icc]
      · simp
      · intro r hr
        simp [hσ r hr, hQ t ht' r hr]
    rw [e, hflux t ht'] at key
    simpa using key
  exact constant_of_has_deriv_right_zero
    (fun t ht' => (hd t ht').continuousAt.continuousWithinAt)
    (fun t ht' => (hd t ⟨ht'.1, ht'.2.le⟩).hasDerivWithinAt) t₁ ⟨ht, le_rfl⟩

/-- Non-vacuity of `IsLOSolution` with a nonzero closure: `φ = 1`, `J = (t, 0)` in the plane
`n = 1`, `σs = σt = 1`, `Q = 0`, `c = 1`, closure `γ = (1 + t, 0)`. -/
example : IsLOSolution (n := 1) 1 0 1 Set.univ (fun _ => 1) (fun _ => 1) (fun _ _ => 0)
    (fun _ _ => 1) (fun t _ => ![t, 0]) (fun t _ => ![1 + t, 0]) := by
  refine ⟨contDiff_const, ?_, ?_, ?_⟩
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_const
  · intro t _ r _
    simp [divergence]
  · intro t _ r _ i
    fin_cases i <;> simp [add_comm]

/-- The flux `(F_x, F_z) = (-√(2/3) φ₁¹, √(1/3) φ₁⁰)` in the `φ₀⁰`-equation of Eq. (24), on the
`xz`-plane `Pt 1` (`x` is the coordinate `0`, `z` the coordinate `1`). -/
noncomputable def momentFlux (u : Moments (Pt 1 → ℝ)) (r : Pt 1) : Pt 1 :=
  ![-(√(2 / 3) * u.φ₁₁ r), √(1 / 3) * u.φ₁₀ r]

/-- **The system (24) as printed**, forward Euler in time and continuous in space, on the rectangle
`[a, b]` of the `xz`-plane, with removal terms `R` in the current equations. -/
structure IsLOFieldStep (a b : Pt 1) (σs σt Q : Pt 1 → ℝ)
    (R : Moments (Pt 1 → ℝ) → (Pt 1 → ℝ) × (Pt 1 → ℝ)) (Δt : ℝ) (γ : (Pt 1 → ℝ) × (Pt 1 → ℝ))
    (u u' : Moments (Pt 1 → ℝ)) : Prop where
  eq₀ : ∀ r ∈ Set.Icc a b, (u'.φ₀₀ r - u.φ₀₀ r) / Δt +
      √(1 / 3) * fderiv ℝ u.φ₁₀ r (Pi.single 1 1) - √(2 / 3) * fderiv ℝ u.φ₁₁ r (Pi.single 0 1) =
    (σs r - σt r) * u.φ₀₀ r + 1 / (2 * √π) * Q r
  eq₁ : ∀ r ∈ Set.Icc a b, (u'.φ₁₀ r - u.φ₁₀ r) / Δt +
      √(1 / 3) * fderiv ℝ u.φ₀₀ r (Pi.single 1 1) = -(R u).1 r + γ.1 r
  eq₂ : ∀ r ∈ Set.Icc a b, (u'.φ₁₁ r - u.φ₁₁ r) / Δt -
      √(1 / 6) * fderiv ℝ u.φ₀₀ r (Pi.single 0 1) = -(R u).2 r + γ.2 r

private theorem divergence_momentFlux {u : Moments (Pt 1 → ℝ)} (h₁₀ : ContDiff ℝ 1 u.φ₁₀)
    (h₁₁ : ContDiff ℝ 1 u.φ₁₁) (r : Pt 1) :
    divergence (momentFlux u) r = √(1 / 3) * fderiv ℝ u.φ₁₀ r (Pi.single 1 1) -
      √(2 / 3) * fderiv ℝ u.φ₁₁ r (Pi.single 0 1) := by
  have hF : ContDiff ℝ 1 (momentFlux u) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact (contDiff_const.mul h₁₁).neg
    · exact contDiff_const.mul h₁₀
  have hd := (hF.differentiable one_ne_zero r).hasFDerivAt
  have coord : ∀ (i : Fin 2) (v : Pt 1),
      fderiv ℝ (momentFlux u) r v i = fderiv ℝ (fun r => momentFlux u r i) r v := by
    intro i v
    rw [(hasFDerivAt_pi'.1 hd i).fderiv]
    rfl
  have d₁₀ : HasFDerivAt (fun r => √(1 / 3) * u.φ₁₀ r) (√(1 / 3) • fderiv ℝ u.φ₁₀ r) r :=
    (h₁₀.differentiable one_ne_zero r).hasFDerivAt.const_mul _
  have d₁₁ : HasFDerivAt (fun r => -(√(2 / 3) * u.φ₁₁ r)) (-(√(2 / 3) • fderiv ℝ u.φ₁₁ r)) r :=
    ((h₁₁.differentiable one_ne_zero r).hasFDerivAt.const_mul _).neg
  have e₀ : (fun r => momentFlux u r 0) = fun r => -(√(2 / 3) * u.φ₁₁ r) := rfl
  have e₁ : (fun r => momentFlux u r 1) = fun r => √(1 / 3) * u.φ₁₀ r := rfl
  rw [divergence, Fin.sum_univ_two, coord, coord, e₀, e₁, d₁₀.fderiv, d₁₁.fderiv]
  simp only [neg_apply, smul_apply, smul_eq_mul]
  ring

/-- **Eq. (24) is globally conservative**, arXiv 2011.06072, Sec. 3.2, for the printed scheme: the
integral of `φ₀⁰` over a rectangle changes in one step by the outflow of the flux and by absorption
and sources, whatever the closure and the removal terms. -/
theorem IsLOFieldStep.integral_balance {a b : Pt 1} {σs σt Q : Pt 1 → ℝ}
    {R : Moments (Pt 1 → ℝ) → (Pt 1 → ℝ) × (Pt 1 → ℝ)} {Δt : ℝ} {γ : (Pt 1 → ℝ) × (Pt 1 → ℝ)}
    {u u' : Moments (Pt 1 → ℝ)} (h : IsLOFieldStep a b σs σt Q R Δt γ u u') (hab : a ≤ b)
    (hΔt : Δt ≠ 0) (h₀₀ : Continuous u.φ₀₀) (h₀₀' : Continuous u'.φ₀₀)
    (h₁₀ : ContDiff ℝ 1 u.φ₁₀) (h₁₁ : ContDiff ℝ 1 u.φ₁₁) :
    ∫ r in Set.Icc a b, u'.φ₀₀ r = (∫ r in Set.Icc a b, u.φ₀₀ r) +
      Δt * ((∫ r in Set.Icc a b, ((σs r - σt r) * u.φ₀₀ r + 1 / (2 * √π) * Q r)) -
        netOutflow a b (momentFlux u)) := by
  have hF : ContDiff ℝ 1 (momentFlux u) := by
    refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · exact (contDiff_const.mul h₁₁).neg
    · exact contDiff_const.mul h₁₀
  have hdiv := continuous_divergence hF
  have hbox : ∀ {f : Pt 1 → ℝ}, Continuous f → IntegrableOn f (Set.Icc a b) := fun hf =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have e : (∫ r in Set.Icc a b, ((σs r - σt r) * u.φ₀₀ r + 1 / (2 * √π) * Q r)) =
      ∫ r in Set.Icc a b, (1 / Δt * (u'.φ₀₀ r - u.φ₀₀ r) + divergence (momentFlux u) r) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have := h.eq₀ r hr
    rw [divergence_momentFlux h₁₀ h₁₁, ← this]
    ring
  have hs : Continuous fun r => 1 / Δt * (u'.φ₀₀ r - u.φ₀₀ r) :=
    continuous_const.mul (h₀₀'.sub h₀₀)
  have e₂ : (∫ r in Set.Icc a b, (1 / Δt * (u'.φ₀₀ r - u.φ₀₀ r) + divergence (momentFlux u) r)) =
      1 / Δt * ((∫ r in Set.Icc a b, u'.φ₀₀ r) - ∫ r in Set.Icc a b, u.φ₀₀ r) +
        netOutflow a b (momentFlux u) := by
    rw [integral_add (hbox hs) (hbox hdiv), integral_const_mul,
      integral_sub (hbox h₀₀') (hbox h₀₀), integral_divergence hab hF]
  rw [e, e₂]
  field_simp
  ring

end PDE

end LeanDLRA.Literature.P2011_06072

import LeanDLRA.Training.Descent
import LeanDLRA.Training.Defs
import LeanDLRA.Matrix.Projectors

/-!
# Factor-wise (LoRA-type) dynamics versus gauge-free Riemannian/DLRT steps

Low-rank training either moves the *factors* of `W = U S Vᵀ` (or `W = B A`, LoRA) by gradient
descent, or moves `W` on the rank-`r` manifold by a gauge-free Riemannian/DLRT step
`W ↦ W - h P(W) ∇L(W)` with the tangent projector `P(W) = tangentProj U V`.  This file compares
the two at the level of exact matrix identities.

## Equilibria of factor-wise dynamics (OP-TR-14)

Simultaneous gradient flow `U̇ = -Z V Sᵀ`, `Ṡ = -Uᵀ Z V`, `V̇ = -Zᵀ U S` on `W = U S Vᵀ`
(`Z = ∇L(W)`) induces `Ẇ = -P̂ Z` with
`P̂ Z = Z V SᵀS Vᵀ + U Uᵀ Z V Vᵀ + U S Sᵀ Uᵀ Z` (`loraPrecond`).

* `inner_loraPrecond`, `loraPrecond_symm`, `inner_loraPrecond_self`: `P̂` is self-adjoint and
  positive semidefinite with `⟪P̂ Z, Z⟫ = ‖Z V Sᵀ‖² + ‖Uᵀ Z V‖² + ‖Sᵀ Uᵀ Z‖²` (no orthonormality
  needed).
* `loraPrecond_eq_zero_iff`: for orthonormal `U`, `V` and **invertible** `S`, `P̂ Z = 0 ⇔
  P(W) Z = 0`: the equilibria of LoRA-type factor descent are exactly the Riemannian stationary
  points.  The negative claims of GeoLoRA (arXiv 2410.18720, Sec. 3) and of the factorised
  momentum paper (arXiv 2506.17475, Thm 4) can therefore only concern singular `S`.
* `exists_loraPrecond_eq_zero_of_not_injective`: conversely, if `S` has a kernel and `r < m`
  there is `Z` with `P̂ Z = 0` but `P(W) Z ≠ 0` (spurious equilibria exist exactly in the singular
  case, as far as the instantaneous operator is concerned).
* `sq_mul_norm_tangentProj_le_inner_loraPrecond`: if `σ_min(S) ≥ s`, the first-order decrease of
  factor descent is at least `s² ‖P(W) Z‖²`; the DLRT step decreases by `‖P(W) Z‖²` independently
  of `s` (`loss_projGradStep_le`).
* `loraPrecond_one`, `loraPrecond_one_mul_transpose`: for `S = 1`, `P̂ = P(W) + 2 P_U(·)P_V`, which
  scales `U Vᵀ` by `3`; so `P̂` is never a projector.
* `norm_sq_tangentProj`: `‖P(W) Z‖² = ‖Uᵀ Z‖² + ‖Z V‖² - ‖Uᵀ Z V‖²`.

What remains of OP-TR-14: a *trajectory* of the factor flow along which `σ_min(S(t)) → 0` and
which converges to a point with `P(W) ∇L ≠ 0` (a dynamical, not instantaneous, counterexample).

## Gauge dependence (OP-TR-15)

* `tangentProj_eq_of_proj_eq`, `projGradStep_tangentProj_eq_of_proj_eq`,
  `mul_mul_transpose_of_orthogonal`: the DLRT step depends on the factorization only through
  `U Uᵀ` and `V Vᵀ`, hence is invariant under the orthogonal gauge `U ↦ U Q`.
* `norm_factorGrad_sub_le`: the factor gradient `B ↦ ∇L(B A) Aᵀ` is `β ‖A‖²`-Lipschitz
  (Frobenius norm, an upper bound for the spectral constant `β ‖A‖₂²`).
* `exists_factorGD_ascent`: for `f(b, a) = (b a - 1)² / 2`, every step size `h > 0` and every
  tolerance `δ > 0`, there is a factorization with `|b a - 1| ≤ δ` from which one factor-GD step
  *increases* `f` — no gauge-uniform step size exists, whereas the DLRT step never ascends for
  `h ≤ 2 / β` (`loss_projGradStep_le_self`).  This turns the unproven statements of
  arXiv 2609.21039, 2306.00897 and 2601.08882 ("non-uniqueness of `W = B A` destabilizes
  training") into a theorem.

## Balancedness (OP-TR-10)

* `hasDerivAt_balance`, `balance_eq_exp`, `balance_eq_const`: along `U̇ = -G V - λ U`,
  `V̇ = -Gᵀ U - λ V` (factorized gradient flow with weight decay `λ (‖U‖² + ‖V‖²) / 2`) the defect
  `D = UᵀU - VᵀV` satisfies `Ḋ = -2 λ D`, hence `D(t) = e^{-2λt} D(0)`; for `λ = 0` it is
  conserved.  `G(t)` is an arbitrary curve, so the result holds for every loss.
* `spectralInit_balanced`: the spectral initialization `U = Û Σ^{1/2}`, `V = V̂ Σ^{1/2}` of
  arXiv 2209.13569 (Sec. 3.2, eq. (3)) gives `UᵀU = VᵀV = Σ` and `U Vᵀ = Û Σ V̂ᵀ`.  This is the
  dimensionally correct balancedness statement; the refutation in 2209.13569 compares `U Uᵀ` with
  `Σ`, which does not test balancedness.
* `factorGD_balance`: one discrete factor-GD step changes `D` by exactly
  `α² ((G V)ᵀ (G V) - (Gᵀ U)ᵀ (Gᵀ U))`, i.e. `O(α²)`.
* `factorGD_product` (arXiv 2209.13569, Sec. 3, eq. (1)): one factor-GD step produces
  `W - α (∇W V Vᵀ + U Uᵀ ∇W) + α² ∇W Wᵀ ∇W`, which is not a GD step on `W`.

What remains of OP-TR-10: why spectral initialization and Frobenius decay *help* (an
implicit-regularization statement), which needs a quantitative model of the loss.

## Augmented bases capture the Riemannian gradient (OP-TR-01)

* `galerkin_tangentProj_of_capture`: if `Û ⊇ [U, ∇L V]` and `V̂ ⊇ [V, ∇Lᵀ U]` (capture identities
  `Û Ûᵀ U = U`, …), the augmented Galerkin projector `Π Z = Û Ûᵀ Z V̂ V̂ᵀ` fixes `P(W) ∇L`.
* `norm_sq_galerkin_eq_of_capture`, `norm_tangentProj_le_of_capture`: hence the Pythagorean split
  `‖Ûᵀ ∇L V̂‖² = ‖P(W) ∇L‖² + ‖Π ∇L - P(W) ∇L‖²` and `‖P(W) ∇L‖ ≤ ‖Ûᵀ ∇L V̂‖`
  (`norm_sq_eq_add_of_absorbs` is the abstract version).
* `leftProj_tangentProj_of_capture`, `norm_tangentProj_le_of_left_capture`: left-only
  augmentation `Û ⊇ [U, ∇L V]` gives `‖P(W) ∇L‖ ≤ ‖Ûᵀ ∇L‖`.
* `exists_leftProj_ne_tangentProj_of_capture`: the identity `P_Û ∇ℓ = P(Y) ∇ℓ` used in the proof
  of abc-PSI (arXiv 2502.03006, Thm 5.9) is false (explicit `2 × 2` example with `U = V = e₁`,
  `∇ℓ = [[1, 0], [1, 1]]`, for which `[U, ∇ℓ V]` spans `ℝ²`); only the inequality holds.

Combined with `exists_tangentGrad_sq_le_of_absorbs` and `frequently_tangentGrad_sq_lt_of_absorbs`
(`Training/Descent.lean`), the stationarity measures of FeDLRT (arXiv 2406.17887, Thm 3),
TDLRT (arXiv 2305.19059, Thm 3.2) and abc-PSI imply Riemannian `ε`-stationarity.

## K-step augmentation equals gradient augmentation

* `capture_kStep_iff` (arXiv 2506.17475, derivation of Algs. 1–2; arXiv 2305.19059, Cor. 2.2;
  arXiv 2406.17887, Lemma 2): with `K(t₀) = U₀ S₀` and `K' = -∇L V₀`, a projector fixing `U₀`
  fixes `K(t₀) + h K'` (`h ≠ 0`) iff it fixes `∇L V₀`; so augmenting by the K-step derivative and
  by the basis gradient give the same space.  (No invertibility of `S₀` is needed.)

The statements `loraPrecond_eq_zero_iff`, `sq_mul_norm_tangentProj_le_inner_loraPrecond`,
`exists_loraPrecond_eq_zero_of_not_injective` and `exists_factorGD_ascent` are proved here (with
general index types).
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

namespace LeanDLRA.FactorizedDynamics

open LeanDLRA

variable {k k' m n : Type*} [Fintype k] [Fintype k'] [Fintype m] [Fintype n]

/-! ### The LoRA operator `P̂` (OP-TR-14) -/

/-- Polarized form of the quadratic form of `P̂`. -/
theorem inner_loraPrecond (U : Matrix m k ℝ) (S : Matrix k k' ℝ) (V : Matrix n k' ℝ)
    (X Y : Matrix m n ℝ) :
    ⟪loraPrecond U S V X, Y⟫ =
      ⟪X * V * Sᵀ, Y * V * Sᵀ⟫ + ⟪Uᵀ * X * V, Uᵀ * Y * V⟫ + ⟪Sᵀ * Uᵀ * X, Sᵀ * Uᵀ * Y⟫ := by
  have h1 : ⟪X * V * (Sᵀ * S) * Vᵀ, Y⟫ = ⟪X * V * Sᵀ, Y * V * Sᵀ⟫ := by
    rw [show X * V * (Sᵀ * S) * Vᵀ = (X * V * Sᵀ) * (S * Vᵀ) by simp only [Matrix.mul_assoc],
      Frobenius.inner_mul_right]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have h2 : ⟪U * Uᵀ * X * V * Vᵀ, Y⟫ = ⟪Uᵀ * X * V, Uᵀ * Y * V⟫ := by
    rw [show U * Uᵀ * X * V * Vᵀ = U * (Uᵀ * X * V) * Vᵀ by simp only [Matrix.mul_assoc],
      Frobenius.inner_mul_right, Frobenius.inner_mul_left]
    simp [Matrix.mul_assoc]
  have h3 : ⟪U * (S * Sᵀ) * Uᵀ * X, Y⟫ = ⟪Sᵀ * Uᵀ * X, Sᵀ * Uᵀ * Y⟫ := by
    rw [show U * (S * Sᵀ) * Uᵀ * X = (U * S) * (Sᵀ * Uᵀ * X) by simp only [Matrix.mul_assoc],
      Frobenius.inner_mul_left]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [loraPrecond, inner_add_left, inner_add_left, h1, h2, h3]

/-- `P̂` is self-adjoint for the Frobenius inner product (OP-TR-14). -/
theorem loraPrecond_symm (U : Matrix m k ℝ) (S : Matrix k k' ℝ) (V : Matrix n k' ℝ)
    (X Y : Matrix m n ℝ) : ⟪loraPrecond U S V X, Y⟫ = ⟪X, loraPrecond U S V Y⟫ := by
  rw [real_inner_comm (loraPrecond U S V Y) X, inner_loraPrecond, inner_loraPrecond,
    real_inner_comm (X * V * Sᵀ), real_inner_comm (Uᵀ * X * V), real_inner_comm (Sᵀ * Uᵀ * X)]

/-- The quadratic form of `P̂` (OP-TR-14):
`⟪P̂ Z, Z⟫ = ‖Z V Sᵀ‖² + ‖Uᵀ Z V‖² + ‖Sᵀ Uᵀ Z‖²`, for arbitrary `U`, `S`, `V`. -/
theorem inner_loraPrecond_self (U : Matrix m k ℝ) (S : Matrix k k' ℝ) (V : Matrix n k' ℝ)
    (Z : Matrix m n ℝ) :
    ⟪loraPrecond U S V Z, Z⟫ = ‖Z * V * Sᵀ‖ ^ 2 + ‖Uᵀ * Z * V‖ ^ 2 + ‖Sᵀ * Uᵀ * Z‖ ^ 2 := by
  rw [inner_loraPrecond, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- `P̂` is positive semidefinite. -/
theorem inner_loraPrecond_self_nonneg (U : Matrix m k ℝ) (S : Matrix k k' ℝ) (V : Matrix n k' ℝ)
    (Z : Matrix m n ℝ) : 0 ≤ ⟪loraPrecond U S V Z, Z⟫ := by
  rw [inner_loraPrecond_self]; positivity

/-- For orthonormal `U`, `V`: `P(W) Z = 0 ⇔ Uᵀ Z = 0 ∧ Z V = 0`. -/
theorem tangentProj_eq_zero_iff [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    tangentProj U V Z = 0 ↔ Uᵀ * Z = 0 ∧ Z * V = 0 := by
  constructor
  · intro h
    have hl : Uᵀ * tangentProj U V Z = Uᵀ * Z := by
      rw [tangentProj_apply]
      simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, hU, Matrix.one_mul]
      abel
    have hr : tangentProj U V Z * V = Z * V := by
      rw [tangentProj_apply]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hV, Matrix.mul_one]
      abel
    rw [h, Matrix.mul_zero] at hl
    rw [h, Matrix.zero_mul] at hr
    exact ⟨hl.symm, hr.symm⟩
  · rintro ⟨hl, hr⟩
    rw [tangentProj_apply]
    simp only [Matrix.mul_assoc, hl, hr, Matrix.mul_zero, Matrix.zero_mul, add_zero, sub_zero]

/-- `‖P(W) Z‖² = ‖Uᵀ Z‖² + ‖Z V‖² - ‖Uᵀ Z V‖²`. -/
theorem norm_sq_tangentProj [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖tangentProj U V Z‖ ^ 2 = ‖Uᵀ * Z‖ ^ 2 + ‖Z * V‖ ^ 2 - ‖Uᵀ * Z * V‖ ^ 2 := by
  rw [← (isOrthProj_tangentProj (m := m) (n := n) hU hV).inner_self_apply, tangentProj_apply,
    inner_sub_left, inner_add_left]
  have h1 : ⟪U * Uᵀ * Z, Z⟫ = ‖Uᵀ * Z‖ ^ 2 := by
    rw [Matrix.mul_assoc, Frobenius.inner_mul_left, real_inner_self_eq_norm_sq]
  have h2 : ⟪Z * V * Vᵀ, Z⟫ = ‖Z * V‖ ^ 2 := by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose, real_inner_self_eq_norm_sq]
  have h3 : ⟪U * Uᵀ * Z * V * Vᵀ, Z⟫ = ‖Uᵀ * Z * V‖ ^ 2 := by
    rw [Frobenius.inner_mul_right, Matrix.transpose_transpose,
      show U * Uᵀ * Z * V = U * (Uᵀ * Z * V) by simp only [Matrix.mul_assoc],
      Frobenius.inner_mul_left, ← real_inner_self_eq_norm_sq, Matrix.mul_assoc Uᵀ Z V]
  rw [h1, h2, h3]

/-- `‖P(W) Z‖² ≤ ‖Uᵀ Z‖² + ‖Z V‖²`. -/
theorem norm_sq_tangentProj_le [DecidableEq k] [DecidableEq k'] {U : Matrix m k ℝ}
    {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Z : Matrix m n ℝ) :
    ‖tangentProj U V Z‖ ^ 2 ≤ ‖Uᵀ * Z‖ ^ 2 + ‖Z * V‖ ^ 2 := by
  rw [norm_sq_tangentProj hU hV]
  nlinarith [sq_nonneg ‖Uᵀ * Z * V‖]

/-- Riemannian stationary points are LoRA equilibria, for every coefficient matrix `S`
(possibly singular): `P(W) Z = 0 ⇒ P̂ Z = 0`. -/
theorem loraPrecond_eq_zero_of_tangentProj_eq_zero [DecidableEq k] [DecidableEq k']
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (S : Matrix k k' ℝ) {Z : Matrix m n ℝ} (hZ : tangentProj U V Z = 0) :
    loraPrecond U S V Z = 0 := by
  obtain ⟨hl, hr⟩ := (tangentProj_eq_zero_iff hU hV Z).1 hZ
  simp only [loraPrecond, Matrix.mul_assoc, hl, hr, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- **LoRA equilibria are Riemannian stationary points when `S` is invertible** (OP-TR-14;
negative claims of arXiv 2410.18720 Sec. 3 and arXiv 2506.17475 Thm 4). For orthonormal `U`,
`V` and invertible `S`, `P̂ Z = 0 ⇔ P(W) Z = 0`.  Proof: the quadratic form forces
`Z V Sᵀ = 0` and `Sᵀ Uᵀ Z = 0`, so `Z V = 0` and `Uᵀ Z = 0`. -/
theorem loraPrecond_eq_zero_iff [DecidableEq k] {U : Matrix m k ℝ} {S : Matrix k k ℝ}
    {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S)
    (Z : Matrix m n ℝ) : loraPrecond U S V Z = 0 ↔ tangentProj U V Z = 0 := by
  refine ⟨fun h => ?_, loraPrecond_eq_zero_of_tangentProj_eq_zero hU hV S⟩
  have h0 := inner_loraPrecond_self U S V Z
  rw [h, inner_zero_left] at h0
  have ha : ‖Z * V * Sᵀ‖ = 0 := by
    nlinarith [sq_nonneg ‖Z * V * Sᵀ‖, sq_nonneg ‖Uᵀ * Z * V‖, sq_nonneg ‖Sᵀ * Uᵀ * Z‖]
  have hb : ‖Sᵀ * Uᵀ * Z‖ = 0 := by
    nlinarith [sq_nonneg ‖Z * V * Sᵀ‖, sq_nonneg ‖Uᵀ * Z * V‖, sq_nonneg ‖Sᵀ * Uᵀ * Z‖]
  rw [norm_eq_zero] at ha hb
  obtain ⟨u, hu⟩ := hS
  have hinv : ((u⁻¹ : (Matrix k k ℝ)ˣ) : Matrix k k ℝ) * (u : Matrix k k ℝ) = 1 := u.inv_mul
  have hinv' : (u : Matrix k k ℝ) * ((u⁻¹ : (Matrix k k ℝ)ˣ) : Matrix k k ℝ) = 1 := u.mul_inv
  rw [tangentProj_eq_zero_iff hU hV]
  constructor
  · have : (((u⁻¹ : (Matrix k k ℝ)ˣ) : Matrix k k ℝ))ᵀ * (Sᵀ * Uᵀ * Z) = Uᵀ * Z := by
      rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hinv',
        Matrix.transpose_one, Matrix.one_mul]
    rw [← this, hb, Matrix.mul_zero]
  · have : Z * V * Sᵀ * (((u⁻¹ : (Matrix k k ℝ)ˣ) : Matrix k k ℝ))ᵀ = Z * V := by
      rw [← hu, Matrix.mul_assoc, ← Matrix.transpose_mul, hinv, Matrix.transpose_one,
        Matrix.mul_one]
    rw [← this, ha, Matrix.zero_mul]

/-- For `S = 1`: `P̂ Z = P(W) Z + 2 U Uᵀ Z V Vᵀ` (OP-TR-14). -/
theorem loraPrecond_one [DecidableEq k] (U : Matrix m k ℝ) (V : Matrix n k ℝ)
    (Z : Matrix m n ℝ) :
    loraPrecond U 1 V Z = tangentProj U V Z + (2 : ℝ) • (U * Uᵀ * Z * V * Vᵀ) := by
  rw [loraPrecond, tangentProj_apply]
  simp only [Matrix.transpose_one, Matrix.mul_one, two_smul]
  abel

/-- `P̂` is not a projector: for `S = 1` and orthonormal `U`, `V` it maps `U Vᵀ` to `3 U Vᵀ`, so
`P̂² ≠ P̂` whenever `U Vᵀ ≠ 0` (OP-TR-14). -/
theorem loraPrecond_one_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    loraPrecond U 1 V (U * Vᵀ) = (3 : ℝ) • (U * Vᵀ) := by
  have h1 : U * Vᵀ * V * Vᵀ = U * Vᵀ := by rw [Matrix.mul_assoc U, hV, Matrix.mul_one]
  have h2 : U * Uᵀ * (U * Vᵀ) = U * Vᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  have h3 : U * Uᵀ * (U * Vᵀ) * V * Vᵀ = U * Vᵀ := by rw [h2, h1]
  simp only [loraPrecond, Matrix.transpose_one, Matrix.mul_one]
  rw [h1, h3, show U * Uᵀ * (U * Vᵀ) = U * Vᵀ from h2]
  module

/-- Row-wise lower bound: if `‖S v‖² ≥ s² ‖v‖²` for all `v`, then `s² ‖A‖² ≤ ‖A Sᵀ‖²`. -/
theorem sq_mul_norm_sq_le_norm_mul_transpose_sq {S : Matrix k k' ℝ} {s : ℝ}
    (hS : ∀ v : k' → ℝ, s ^ 2 * (v ⬝ᵥ v) ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v)) (A : Matrix m k' ℝ) :
    s ^ 2 * ‖A‖ ^ 2 ≤ ‖A * Sᵀ‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := hS (A i)
  have hrow : ∀ j, (S *ᵥ A i) j = (A * Sᵀ) i j := fun j => by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  simp only [dotProduct, hrow] at h
  simpa only [sq] using h

/-- **LoRA descent is controlled by `σ_min(S)²`** (OP-TR-15, OP-SB-55). If `‖S v‖ ≥ s ‖v‖` and
`‖Sᵀ v‖ ≥ s ‖v‖`, the first-order decrease of factor-wise descent satisfies
`s² ‖P(W) Z‖² ≤ ⟪P̂ Z, Z⟫`, whereas the DLRT step decreases the loss at first order by
`‖P(W) Z‖²` independently of `s`. -/
theorem sq_mul_norm_tangentProj_le_inner_loraPrecond [DecidableEq k] [DecidableEq k']
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {s : ℝ} (hS : ∀ v : k' → ℝ, s ^ 2 * (v ⬝ᵥ v) ≤ (S *ᵥ v) ⬝ᵥ (S *ᵥ v))
    (hSt : ∀ v : k → ℝ, s ^ 2 * (v ⬝ᵥ v) ≤ (Sᵀ *ᵥ v) ⬝ᵥ (Sᵀ *ᵥ v)) (Z : Matrix m n ℝ) :
    s ^ 2 * ‖tangentProj U V Z‖ ^ 2 ≤ ⟪loraPrecond U S V Z, Z⟫ := by
  have h1 := sq_mul_norm_sq_le_norm_mul_transpose_sq hS (Z * V)
  have h2 := sq_mul_norm_sq_le_norm_mul_transpose_sq hSt (Zᵀ * U)
  have e2 : ‖Zᵀ * U * Sᵀᵀ‖ = ‖Sᵀ * Uᵀ * Z‖ := by
    rw [← Frobenius.norm_transpose (Sᵀ * Uᵀ * Z)]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have e3 : ‖Zᵀ * U‖ = ‖Uᵀ * Z‖ := by
    rw [← Frobenius.norm_transpose (Uᵀ * Z), Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e2, e3] at h2
  have h3 := norm_sq_tangentProj_le hU hV Z
  rw [inner_loraPrecond_self]
  nlinarith [sq_nonneg s, sq_nonneg ‖Uᵀ * Z * V‖]

/-- **Singular `S` creates spurious LoRA equilibria** (OP-TR-14). If `S x = 0` for some `x ≠ 0`
and `r < m`, then `Z = u⊥ (V x)ᵀ` with `Uᵀ u⊥ = 0`, `u⊥ ≠ 0` satisfies `P̂ Z = 0` but
`P(W) Z ≠ 0`. -/
theorem exists_loraPrecond_eq_zero_of_not_injective [DecidableEq k] [DecidableEq k']
    {U : Matrix m k ℝ} {S : Matrix k k' ℝ} {V : Matrix n k' ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hr : Fintype.card k < Fintype.card m) (hS : ∃ v : k' → ℝ, v ≠ 0 ∧ S *ᵥ v = 0) :
    ∃ Z : Matrix m n ℝ, loraPrecond U S V Z = 0 ∧ tangentProj U V Z ≠ 0 := by
  classical
  obtain ⟨x, hx0, hx⟩ := hS
  have hker : LinearMap.ker (Matrix.mulVecLin Uᵀ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hr)
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu
  have hxV : (V *ᵥ x) ᵥ* V = x := by
    rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
  refine ⟨Matrix.vecMulVec u (V *ᵥ x), ?_, ?_⟩
  · have hl : Uᵀ * Matrix.vecMulVec u (V *ᵥ x) = 0 := by
      rw [Matrix.mul_vecMulVec, hu]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have hr' : Matrix.vecMulVec u (V *ᵥ x) * V * Sᵀ = 0 := by
      rw [Matrix.vecMulVec_mul, hxV, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hx]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have e1 : Matrix.vecMulVec u (V *ᵥ x) * V * (Sᵀ * S) * Vᵀ =
        Matrix.vecMulVec u (V *ᵥ x) * V * Sᵀ * (S * Vᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [loraPrecond, e1, hr', Matrix.zero_mul, Matrix.mul_assoc U Uᵀ, hl,
      Matrix.mul_assoc (U * (S * Sᵀ)), hl]
    simp
  · intro h
    have hZV := ((tangentProj_eq_zero_iff hU hV _).1 h).2
    rw [Matrix.vecMulVec_mul, hxV] at hZV
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx0
    have := congrFun (congrFun hZV i) j
    simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at this
    exact mul_ne_zero hi hj this

/-! ### Gauge dependence (OP-TR-15) -/

/-- The tangent projector depends on the factors only through `U Uᵀ` and `V Vᵀ` (OP-TR-15:
gauge freedom of the Riemannian/DLRT step). -/
theorem tangentProj_eq_of_proj_eq {k₁ k₁' : Type*} [Fintype k₁] [Fintype k₁']
    {U : Matrix m k ℝ} {U₁ : Matrix m k₁ ℝ} {V : Matrix n k' ℝ} {V₁ : Matrix n k₁' ℝ}
    (hU : U * Uᵀ = U₁ * U₁ᵀ) (hV : V * Vᵀ = V₁ * V₁ᵀ) :
    (tangentProj U V : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) = tangentProj U₁ V₁ := by
  simp only [tangentProj, leftProj, rightProj, hU, hV]

/-- **Gauge invariance of the DLRT step** (OP-TR-15): two factorizations with the same column-
and row-space projectors produce the same projected gradient step. -/
theorem projGradStep_tangentProj_eq_of_proj_eq {k₁ k₁' : Type*} [Fintype k₁] [Fintype k₁']
    {U : Matrix m k ℝ} {U₁ : Matrix m k₁ ℝ} {V : Matrix n k' ℝ} {V₁ : Matrix n k₁' ℝ}
    (hU : U * Uᵀ = U₁ * U₁ᵀ) (hV : V * Vᵀ = V₁ * V₁ᵀ) (g : Matrix m n ℝ → Matrix m n ℝ)
    (h : ℝ) (W : Matrix m n ℝ) :
    projGradStep (tangentProj U V) g h W = projGradStep (tangentProj U₁ V₁) g h W := by
  rw [tangentProj_eq_of_proj_eq hU hV]

omit [Fintype m] in
/-- Orthogonal gauge transformations do not change `U Uᵀ`. -/
theorem mul_mul_transpose_of_orthogonal [DecidableEq k] (U : Matrix m k ℝ) {Q : Matrix k k ℝ}
    (hQ : Q * Qᵀ = 1) : U * Q * (U * Q)ᵀ = U * Uᵀ := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ, Matrix.one_mul]

/-- Block Lipschitz bound of the factor gradient (OP-TR-15): if `∇L` is `β`-Lipschitz, then
`B ↦ ∇L(B A) Aᵀ` is `β ‖A‖²`-Lipschitz.  Along the gauge orbit `(B G, G⁻¹ A)` this constant
is unbounded (see `exists_factorGD_ascent` for the resulting failure of any fixed step size). -/
theorem norm_factorGrad_sub_le {g : Matrix m n ℝ → Matrix m n ℝ} {β : ℝ}
    (hg : ∀ X Y, ‖g X - g Y‖ ≤ β * ‖X - Y‖) (hβ : 0 ≤ β) (A : Matrix k n ℝ)
    (B₁ B₂ : Matrix m k ℝ) :
    ‖g (B₁ * A) * Aᵀ - g (B₂ * A) * Aᵀ‖ ≤ β * ‖A‖ ^ 2 * ‖B₁ - B₂‖ := by
  rw [← Matrix.sub_mul]
  calc ‖(g (B₁ * A) - g (B₂ * A)) * Aᵀ‖ ≤ ‖g (B₁ * A) - g (B₂ * A)‖ * ‖Aᵀ‖ :=
        Frobenius.norm_mul_le _ _
    _ ≤ β * ‖B₁ * A - B₂ * A‖ * ‖A‖ := by
        rw [Frobenius.norm_transpose]
        exact mul_le_mul_of_nonneg_right (hg _ _) (norm_nonneg _)
    _ ≤ β * (‖B₁ - B₂‖ * ‖A‖) * ‖A‖ := by
        rw [← Matrix.sub_mul]
        gcongr
        exact Frobenius.norm_mul_le _ _
    _ = β * ‖A‖ ^ 2 * ‖B₁ - B₂‖ := by ring

/-- **No gauge-uniform step size for factor gradient descent** (OP-TR-15; claims of
arXiv 2609.21039, 2601.08882). For `f(b, a) = (b a - 1)² / 2`, every `h > 0` and `δ > 0`, there
is a factorization `b a = 1 - min δ (1/2)` (with `a² = 3 / h`) from which one gradient step on the
factors increases `f`. -/
theorem exists_factorGD_ascent {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    ∃ b a : ℝ, |b * a - 1| ≤ δ ∧
      (b * a - 1) ^ 2 / 2 <
        ((b - h * ((b * a - 1) * a)) * (a - h * ((b * a - 1) * b)) - 1) ^ 2 / 2 := by
  set d := min δ (1 / 2) with hd
  have hd0 : 0 < d := lt_min hδ (by norm_num)
  have hd1 : d ≤ 1 / 2 := min_le_right _ _
  set t := Real.sqrt (3 / h) with ht
  have ht2 : t ^ 2 = 3 / h := Real.sq_sqrt (by positivity)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0] at ht2; have : (0 : ℝ) < 3 / h := by positivity
    linarith [show (0 : ℝ) ^ 2 = 0 by ring]
  set c := 1 - d
  refine ⟨c / t, t, ?_, ?_⟩
  · have : c / t * t - 1 = -d := by field_simp; ring
    rw [this, abs_neg, abs_of_pos hd0]; exact min_le_left _ _
  · have hba : c / t * t = c := by field_simp
    set b := c / t
    have key : (b - h * ((b * t - 1) * t)) * (t - h * ((b * t - 1) * b)) - 1 =
        (b * t - 1) * (1 - h * (t ^ 2 + b ^ 2) + h ^ 2 * (b * t - 1) * (b * t)) := by ring
    rw [key, hba]
    have hF : 1 - h * (t ^ 2 + b ^ 2) + h ^ 2 * (c - 1) * c ≤ -2 := by
      have e : h * t ^ 2 = 3 := by rw [ht2]; field_simp
      have hc : 0 ≤ c := by simp only [c]; linarith
      nlinarith [sq_nonneg b, mul_nonneg (mul_nonneg (sq_nonneg h) hd0.le) hc]
    have hcd : c - 1 = -d := by simp only [c]; ring
    rw [hcd] at hF ⊢
    have hF2 : 4 ≤ (1 - h * (t ^ 2 + b ^ 2) + h ^ 2 * -d * c) ^ 2 := by nlinarith
    have : 0 < d ^ 2 := by positivity
    nlinarith

/-! ### Balancedness of the factorized gradient flow (OP-TR-10) -/

/-- Derivative of the balancedness defect `D = UᵀU - VᵀV` along the factorized gradient flow
with weight decay, `U̇ = -G V - λ U`, `V̇ = -Gᵀ U - λ V`: `Ḋ = -2 λ D` (OP-TR-10). -/
theorem hasDerivAt_balance {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ}
    {G : ℝ → Matrix m n ℝ} {lam t : ℝ}
    (hU : HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) :
    HasDerivAt (fun t => (U t)ᵀ * U t - (V t)ᵀ * V t)
      ((-2 * lam) • ((U t)ᵀ * U t - (V t)ᵀ * V t)) t := by
  have h1 := Frobenius.hasDerivAt_mul (Frobenius.hasDerivAt_transpose hU) hU
  have h2 := Frobenius.hasDerivAt_mul (Frobenius.hasDerivAt_transpose hV) hV
  convert h1.sub h2 using 1
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  module

/-- **Exponential decay of the balancedness defect** (OP-TR-10): `D(t) = e^{-2λt} D(0)` for
every curve `G(t)`, so balancedness is attracting under weight decay. -/
theorem balance_eq_exp {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ}
    {G : ℝ → Matrix m n ℝ} {lam : ℝ}
    (hU : ∀ t, HasDerivAt U (-(G t * V t) - lam • U t) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t) - lam • V t) t) (t : ℝ) :
    (U t)ᵀ * U t - (V t)ᵀ * V t = Real.exp (-2 * lam * t) • ((U 0)ᵀ * U 0 - (V 0)ᵀ * V 0) := by
  set D : ℝ → Matrix k k ℝ := fun t => (U t)ᵀ * U t - (V t)ᵀ * V t with hDdef
  have hE : ∀ s, HasDerivAt (fun s => Real.exp (2 * lam * s) • D s) 0 s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (2 * lam * s)) (Real.exp (2 * lam * s) * (2 * lam))
        s := by
      simpa using ((hasDerivAt_id' s).const_mul (2 * lam)).exp
    convert he.smul (hasDerivAt_balance (hU s) (hV s)) using 1
    module
  have hc := is_const_of_deriv_eq_zero (fun s => (hE s).differentiableAt)
    (fun s => (hE s).deriv) t 0
  simp only [mul_zero, Real.exp_zero, one_smul] at hc
  change D t = Real.exp (-2 * lam * t) • D 0
  rw [← hc, smul_smul, ← Real.exp_add, show -2 * lam * t + 2 * lam * t = 0 by ring,
    Real.exp_zero, one_smul]

/-- **Conservation of balancedness** (OP-TR-10; arXiv 2209.13569 Sec. 3.2): without weight
decay `UᵀU - VᵀV` is constant along `U̇ = -G V`, `V̇ = -Gᵀ U`. -/
theorem balance_eq_const {U : ℝ → Matrix m k ℝ} {V : ℝ → Matrix n k ℝ}
    {G : ℝ → Matrix m n ℝ} (hU : ∀ t, HasDerivAt U (-(G t * V t)) t)
    (hV : ∀ t, HasDerivAt V (-((G t)ᵀ * U t)) t) (t : ℝ) :
    (U t)ᵀ * U t - (V t)ᵀ * V t = (U 0)ᵀ * U 0 - (V 0)ᵀ * V 0 := by
  have := balance_eq_exp (G := G) (lam := 0) (fun t => by simpa using hU t)
    (fun t => by simpa using hV t) t
  simpa using this

/-- **Spectral initialization is balanced** (arXiv 2209.13569 Sec. 3.2, eq. (3); OP-TR-10): for
orthonormal `Û`, `V̂` and symmetric `R` (`R = Σ^{1/2}`), the factors `U = Û R`, `V = V̂ R` satisfy
`UᵀU = VᵀV = R R` and `U Vᵀ = Û (R R) V̂ᵀ`. -/
theorem spectralInit_balanced [DecidableEq k] {Uh : Matrix m k ℝ} {Vh : Matrix n k ℝ}
    (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1) {R : Matrix k k ℝ} (hR : Rᵀ = R) :
    (Uh * R)ᵀ * (Uh * R) = R * R ∧ (Vh * R)ᵀ * (Vh * R) = R * R ∧
      Uh * R * (Vh * R)ᵀ = Uh * (R * R) * Vhᵀ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hR, Matrix.mul_assoc, ← Matrix.mul_assoc Uhᵀ, hU, Matrix.one_mul]
  · rw [Matrix.transpose_mul, hR, Matrix.mul_assoc, ← Matrix.mul_assoc Vhᵀ, hV, Matrix.one_mul]
  · rw [Matrix.transpose_mul, hR]; simp only [Matrix.mul_assoc]

omit [Fintype k] in
/-- **Discrete factor GD conserves balancedness up to `O(α²)`** (OP-TR-10): one step
`U ↦ U - α G V`, `V ↦ V - α Gᵀ U` changes `UᵀU - VᵀV` by exactly
`α² ((G V)ᵀ (G V) - (Gᵀ U)ᵀ (Gᵀ U))`. -/
theorem factorGD_balance (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) (α : ℝ) :
    (U - α • (G * V))ᵀ * (U - α • (G * V)) - (V - α • (Gᵀ * U))ᵀ * (V - α • (Gᵀ * U)) =
      (Uᵀ * U - Vᵀ * V) + α ^ 2 • ((G * V)ᵀ * (G * V) - (Gᵀ * U)ᵀ * (Gᵀ * U)) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc]
  module

/-- **One factor GD step is not a GD step on `W`** (arXiv 2209.13569, Sec. 3, eq. (1)): with
`W = U Vᵀ`, the step gives `W - α (∇W V Vᵀ + U Uᵀ ∇W) + α² ∇W Wᵀ ∇W`. -/
theorem factorGD_product (U : Matrix m k ℝ) (V : Matrix n k ℝ) (G : Matrix m n ℝ) (α : ℝ) :
    (U - α • (G * V)) * (V - α • (Gᵀ * U))ᵀ =
      U * Vᵀ - α • (G * V * Vᵀ + U * Uᵀ * G) + α ^ 2 • (G * (U * Vᵀ)ᵀ * G) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_assoc, smul_add]
  module

/-! ### Augmented bases capture the Riemannian gradient (OP-TR-01) -/

/-- Abstract Pythagorean split (OP-TR-01): if the orthogonal projector `Q` fixes `T v` for an
orthogonal projector `T`, then `‖Q v‖² = ‖T v‖² + ‖Q v - T v‖²`. -/
theorem norm_sq_eq_add_of_absorbs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T Q : E →L[ℝ] E} (hT : IsOrthProj T) (hQ : IsOrthProj Q) {v : E} (hv : Q (T v) = T v) :
    ‖Q v‖ ^ 2 = ‖T v‖ ^ 2 + ‖Q v - T v‖ ^ 2 := by
  have h0 : ⟪T v, Q v - T v⟫ = 0 := by
    rw [inner_sub_right, ← hQ.symm, hv, real_inner_self_eq_norm_sq, hT.inner_self_apply]
    ring
  have := norm_add_sq_real (T v) (Q v - T v)
  rw [add_sub_cancel, h0] at this
  linarith

/-- The Galerkin projector `Z ↦ Û Ûᵀ Z V̂ V̂ᵀ` of bases augmented by `[U, G V]` and `[V, Gᵀ U]`
fixes the Riemannian gradient `P(W) G` (OP-TR-01). -/
theorem galerkin_tangentProj_of_capture {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U) (hUG : Uh * Uhᵀ * (G * V) = G * V)
    (hVV : Vh * Vhᵀ * V = V) (hVG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U) :
    leftProj Uh (rightProj Vh (tangentProj U V G)) = tangentProj U V G := by
  have hVV' : Vᵀ * (Vh * Vhᵀ) = Vᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hVV
  have hVG' : Uᵀ * G * (Vh * Vhᵀ) = Uᵀ * G := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hVG
  rw [leftProj_apply, rightProj_apply', tangentProj_apply]
  set P := Uh * Uhᵀ
  set Q := Vh * Vhᵀ
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub]
  have e1 : P * (U * Uᵀ * G * Q) = (P * U) * (Uᵀ * G * Q) := by simp only [Matrix.mul_assoc]
  have e2 : P * (G * V * Vᵀ * Q) = (P * (G * V)) * (Vᵀ * Q) := by simp only [Matrix.mul_assoc]
  have e3 : P * (U * Uᵀ * G * V * Vᵀ * Q) = (P * U) * (Uᵀ * G * V) * (Vᵀ * Q) := by
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, hUU, hUG, hVV', hVG']
  simp only [Matrix.mul_assoc]

/-- **The augmented Galerkin gradient dominates the Riemannian gradient** (OP-TR-01;
FeDLRT arXiv 2406.17887 Thm 3, TDLRT arXiv 2305.19059 Thm 3.2, abc-PSI arXiv 2502.03006 Thm 5.9):
`‖Ûᵀ G V̂‖² = ‖P(W) G‖² + ‖Û Ûᵀ G V̂ V̂ᵀ - P(W) G‖²`. -/
theorem norm_sq_galerkin_eq_of_capture {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k] [DecidableEq k'] [DecidableEq k₁] [DecidableEq k₂]
    {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U) (hUG : Uh * Uhᵀ * (G * V) = G * V)
    (hVV : Vh * Vhᵀ * V = V) (hVG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U) :
    ‖Uhᵀ * G * Vh‖ ^ 2 = ‖tangentProj U V G‖ ^ 2 +
      ‖Uh * Uhᵀ * G * Vh * Vhᵀ - tangentProj U V G‖ ^ 2 := by
  have hQ := isOrthProj_leftProj_mul_rightProj (m := m) (n := n) hUh hVh
  have habs : (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ)
      (tangentProj U V G) = tangentProj U V G :=
    galerkin_tangentProj_of_capture hUU hUG hVV hVG
  have h := norm_sq_eq_add_of_absorbs (isOrthProj_tangentProj hU hV) hQ habs
  have e : (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) G =
      Uh * (Uhᵀ * G * Vh) * Vhᵀ := by
    simp [Matrix.mul_assoc]
  have e' : (leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) G =
      Uh * Uhᵀ * G * Vh * Vhᵀ := by
    simp [Matrix.mul_assoc]
  have hn : ‖Uhᵀ * G * Vh‖ =
      ‖(leftProj Uh * rightProj Vh : Matrix m n ℝ →L[ℝ] Matrix m n ℝ) G‖ := by
    rw [e, Frobenius.norm_mul_transpose_of_orthonormal hVh,
      Frobenius.norm_mul_of_orthonormal hUh]
  rw [hn, ← e']
  exact h

/-- `‖P(W) G‖ ≤ ‖Ûᵀ G V̂‖` for augmented bases (OP-TR-01): the augmented-coefficient stationarity
measure controls the Riemannian one. -/
theorem norm_tangentProj_le_of_capture {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k] [DecidableEq k'] [DecidableEq k₁] [DecidableEq k₂]
    {Uh : Matrix m k₁ ℝ} {Vh : Matrix n k₂ ℝ} {U : Matrix m k ℝ} {V : Matrix n k' ℝ}
    (hUh : Uhᵀ * Uh = 1) (hVh : Vhᵀ * Vh = 1) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U) (hUG : Uh * Uhᵀ * (G * V) = G * V)
    (hVV : Vh * Vhᵀ * V = V) (hVG : Vh * Vhᵀ * (Gᵀ * U) = Gᵀ * U) :
    ‖tangentProj U V G‖ ≤ ‖Uhᵀ * G * Vh‖ := by
  have h := norm_sq_galerkin_eq_of_capture hUh hVh hU hV hUU hUG hVV hVG
  nlinarith [sq_nonneg ‖Uh * Uhᵀ * G * Vh * Vhᵀ - tangentProj U V G‖,
    norm_nonneg (tangentProj U V G), norm_nonneg (Uhᵀ * G * Vh)]

/-- Left-only augmentation `Û ⊇ [U, G V]`: `Û Ûᵀ` fixes the Riemannian gradient `P(W) G`
(OP-TR-01). -/
theorem leftProj_tangentProj_of_capture {k₁ : Type*} [Fintype k₁] {Uh : Matrix m k₁ ℝ}
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U)
    (hUG : Uh * Uhᵀ * (G * V) = G * V) :
    leftProj Uh (tangentProj U V G) = tangentProj U V G := by
  rw [leftProj_apply, tangentProj_apply]
  simp only [Matrix.mul_add, Matrix.mul_sub]
  have e1 : Uh * Uhᵀ * (U * Uᵀ * G) = Uh * Uhᵀ * U * (Uᵀ * G) := by simp only [Matrix.mul_assoc]
  have e2 : Uh * Uhᵀ * (G * V * Vᵀ) = Uh * Uhᵀ * (G * V) * Vᵀ := by simp only [Matrix.mul_assoc]
  have e3 : Uh * Uhᵀ * (U * Uᵀ * G * V * Vᵀ) = Uh * Uhᵀ * U * (Uᵀ * G * V * Vᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, hUU, hUG]
  simp only [Matrix.mul_assoc]

/-- Left-only augmentation: `‖P(W) G‖ ≤ ‖Ûᵀ G‖` (OP-TR-01). -/
theorem norm_tangentProj_le_of_left_capture {k₁ : Type*} [Fintype k₁]
    [DecidableEq k] [DecidableEq k'] [DecidableEq k₁] {Uh : Matrix m k₁ ℝ}
    {U : Matrix m k ℝ} {V : Matrix n k' ℝ} (hUh : Uhᵀ * Uh = 1) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {G : Matrix m n ℝ} (hUU : Uh * Uhᵀ * U = U)
    (hUG : Uh * Uhᵀ * (G * V) = G * V) :
    ‖tangentProj U V G‖ ≤ ‖Uhᵀ * G‖ := by
  have h := norm_apply_le_of_absorbs (isOrthProj_tangentProj (m := m) (n := n) hU hV)
    (isOrthProj_leftProj hUh) (leftProj_tangentProj_of_capture hUU hUG)
  rwa [leftProj_apply, Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hUh] at h

/-- **The identity `P_Û ∇ℓ = P(Y) ∇ℓ` used in the proof of abc-PSI (arXiv 2502.03006, Thm 5.9)
is false** (OP-TR-01): for `U = V = e₁`, `∇ℓ = [[1, 0], [1, 1]]` and `Û = I` (an orthonormal
basis of `span[U, ∇ℓ V] = ℝ²`) the capture identities hold but `Û Ûᵀ ∇ℓ ≠ P(Y) ∇ℓ`. -/
theorem exists_leftProj_ne_tangentProj_of_capture :
    ∃ (U V : Matrix (Fin 2) (Fin 1) ℝ) (Uh G : Matrix (Fin 2) (Fin 2) ℝ),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Uhᵀ * Uh = 1 ∧ Uh * Uhᵀ * U = U ∧
        Uh * Uhᵀ * (G * V) = G * V ∧ leftProj Uh G ≠ tangentProj U V G := by
  refine ⟨!![1; 0], !![1; 0], 1, !![1, 0; 1, 1], ?_, ?_, by simp, by simp, by simp, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]
  · intro h
    have := congrFun (congrFun h 1) 1
    norm_num [tangentProj_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, Matrix.transpose_apply] at this

/-! ### Augmentation by the K-step derivative equals gradient augmentation -/

/-- Augmenting by the K-step derivative is augmenting by the basis gradient (arXiv 2506.17475,
Algs. 1–2; arXiv 2305.19059, Cor. 2.2; arXiv 2406.17887, Lemma 2): for `K(t₀) = U₀ S₀`,
`K' = -∇L V₀` (`GV = ∇L V₀`) and `h ≠ 0`, a projector `P` with `P U₀ = U₀` fixes
`K(t₀) + h K'` iff it fixes `∇L V₀`. -/
theorem capture_kStep_iff {P : Matrix m m ℝ} {U₀ : Matrix m k ℝ} (S₀ : Matrix k k ℝ)
    (GV : Matrix m k ℝ) {h : ℝ} (hh : h ≠ 0) (hP : P * U₀ = U₀) :
    P * (U₀ * S₀ - h • GV) = U₀ * S₀ - h • GV ↔ P * GV = GV := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hP, Matrix.mul_smul, sub_right_inj]
  exact (smul_right_injective _ hh).eq_iff

/-! ### Non-degenerate instances -/

/-- The hypotheses of `loraPrecond_eq_zero_iff` are satisfiable with a nonzero gradient: `U = V =
e₁ ∈ ℝ^{2×1}`, `S = 2`, `Z = e₂ e₂ᵀ` is a (normal) direction with `P̂ Z = 0`. -/
example : loraPrecond (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) !![2] !![1; 0]
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [loraPrecond, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply]

end LeanDLRA.FactorizedDynamics

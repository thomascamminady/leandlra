import LeanDLRA.Research.ImplicitBUGEnergyProjection

/-!
# Implicit BUG steps with rational Krylov bases: the error is an ADI residual

For the field `F(Z) = -BᵀB Z - Z CᵀC` the S-step of the BUG integrator with backward Euler
substeps is the energy projection of the backward Euler step `A` on the full matrix,
`A + h (BᵀB A + A CᵀC) = Y₀`, onto the tensor space `{U₁ G V₁ᵀ}` of the new bases
(`IsMatrixImplicitBUGStep.energy_sub_le_of_sylvester`). The equation for `A` is a Sylvester
equation with the right-hand side `Y₀ = U₀ S₀ V₀ᵀ` of rank `r`. Its alternating direction
implicit (ADI) iteration with `k` pairs of shifts, started at zero, has the factored form

  `W = ∑ j < k, (sⱼ + tⱼ - 1) Zⱼ S₀ Yⱼᵀ`,
  `(sⱼ + h BᵀB) Zⱼ = Ûⱼ`,  `Ûⱼ₊₁ = Ûⱼ - (sⱼ + tⱼ - 1) Zⱼ`,  `Û₀ = U₀`,
  `(tⱼ + h CᵀC) Yⱼ = V̂ⱼ`,  `V̂ⱼ₊₁ = V̂ⱼ - (sⱼ + tⱼ - 1) Yⱼ`,  `V̂₀ = V₀`,

and its residual is `Y₀ - (W + h (BᵀB W + W CᵀC)) = Ûₖ S₀ V̂ₖᵀ`, where
`Ûₖ = ∏ⱼ (h BᵀB + 1 - tⱼ) (h BᵀB + sⱼ)⁻¹ U₀` and likewise `V̂ₖ`. If the new bases contain the
columns of all `Zⱼ` and `Yⱼ` (shifted resolvents applied to the old bases: a rational Krylov
space), then `W` lies in the tensor space, and the energy error of the step against the full
backward Euler step is at most the squared norm of the ADI residual. The stiffness enters only
through the rational function of the shifts.

With one pair of shifts `s = t = 1` the bases are `(1 + h BᵀB)⁻¹ U₀` and `(1 + h CᵀC)⁻¹ V₀`
(as many linear solves as the K- and L-step), and the bound is
`‖(h BᵀB Z) S₀ (h CᵀC Y)ᵀ‖²`: a product of the rough parts of both bases.

## Main results

* `IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_residual_of_sylvester`: the energy error of
  the step is at most the squared residual norm of every matrix `U₁ G V₁ᵀ`.
* `IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_adi_of_sylvester`: bases that contain the ADI
  factors; the bound is the squared norm of the ADI residual `Ûₖ S₀ V̂ₖᵀ`.
* `IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_resolvent_of_sylvester`: one pair of shifts.
* `norm_implicitBUG_run_sub_le_of_sylvester_residual`: a run with truncation tolerances `ϑⱼ`
  stays within `∑ (δⱼ + ϑⱼ)` of the backward Euler run on the full matrix, where `δⱼ` bounds a
  residual of step `j`; no bound of `B`, `C` enters.
* `exists_isMatrixImplicitBUGStep_of_sylvester`: for all orthonormal old and new bases a step
  exists (`h ≥ 0`).
* `RationalKrylovExample.exists_isMatrixImplicitBUGStep_norm_sub_le`: in the `3 × 2` family of
  `StiffAugmentedExample` (where every step with the column basis in the span of `U₀` and `K₁`
  is at distance `≥ 1/3` from the solution) the step with the resolvent bases is within
  `‖Y₀ - X‖ + 2 |s t|` of the solution, for all `h`, `μ`, `lam ≥ 0`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
* ADI with shifts and the size of its rational function: arXiv 1609.09494 (Beckermann,
  Townsend), Theorem 2.1, the remark after it, and Corollary 3.2.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

open Matrix

namespace LeanDLRA

namespace ImplicitBUGRationalKrylov

variable {m n p q ι κ : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype ι]
  [Fintype κ]

/-- `⟪BᵀB Z, W⟫ = ⟪B Z, B W⟫`. -/
private theorem rk_inner_gram_mul (B : Matrix p m ℝ) (Z W : Matrix m n ℝ) :
    ⟪Bᵀ * B * Z, W⟫ = ⟪B * Z, B * W⟫ := by
  rw [Matrix.mul_assoc, Frobenius.inner_mul_left, Matrix.transpose_transpose]

/-- `⟪Z CᵀC, W⟫ = ⟪Z Cᵀ, W Cᵀ⟫`. -/
private theorem rk_inner_mul_gram (C : Matrix q n ℝ) (Z W : Matrix m n ℝ) :
    ⟪Z * (Cᵀ * C), W⟫ = ⟪Z * Cᵀ, W * Cᵀ⟫ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]

/-- The energy of `D` is the inner product of `D + h (BᵀB D + D CᵀC)` with `D`. -/
private theorem rk_energy_eq_inner (B : Matrix p m ℝ) (C : Matrix q n ℝ) (h : ℝ)
    (D : Matrix m n ℝ) :
    ‖D‖ ^ 2 + h * ‖B * D‖ ^ 2 + h * ‖D * Cᵀ‖ ^ 2 =
      ⟪D + h • (Bᵀ * B * D + D * (Cᵀ * C)), D⟫ := by
  rw [inner_add_left, real_inner_smul_left, inner_add_left, rk_inner_gram_mul,
    rk_inner_mul_gram, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

/-- The energy of `D` is at most the squared norm of `D + h (BᵀB D + D CᵀC)`, and so is the
squared norm of `D`. -/
private theorem rk_energy_le_sq_norm (B : Matrix p m ℝ) (C : Matrix q n ℝ) {h : ℝ} (hh : 0 ≤ h)
    (D : Matrix m n ℝ) :
    ‖D‖ ^ 2 + h * ‖B * D‖ ^ 2 + h * ‖D * Cᵀ‖ ^ 2 ≤
      ‖D + h • (Bᵀ * B * D + D * (Cᵀ * C))‖ ^ 2 := by
  have h1 := rk_energy_eq_inner B C h D
  have h2 := real_inner_le_norm (D + h • (Bᵀ * B * D + D * (Cᵀ * C))) D
  have h3 := mul_nonneg hh (sq_nonneg ‖B * D‖)
  have h4 := mul_nonneg hh (sq_nonneg ‖D * Cᵀ‖)
  have h5 := norm_nonneg D
  have h6 := norm_nonneg (D + h • (Bᵀ * B * D + D * (Cᵀ * C)))
  rcases h5.eq_or_lt with h0 | hpos
  · rw [← h0] at h2
    nlinarith
  · have h7 : ‖D‖ ≤ ‖D + h • (Bᵀ * B * D + D * (Cᵀ * C))‖ := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    nlinarith

/-- The backward Euler step on the full matrix does not increase the norm. -/
private theorem rk_norm_le_of_resolvent {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}
    (hh : 0 ≤ h) {D Z : Matrix m n ℝ} (hD : D + h • (Bᵀ * B * D + D * (Cᵀ * C)) = Z) :
    ‖D‖ ≤ ‖Z‖ := by
  have h1 := rk_energy_le_sq_norm B C hh D
  rw [hD] at h1
  have h3 := mul_nonneg hh (sq_nonneg ‖B * D‖)
  have h4 := mul_nonneg hh (sq_nonneg ‖D * Cᵀ‖)
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg D, norm_nonneg Z]

/-- The energy distance of `W` to the full backward Euler step is at most the squared norm of
the residual of `W`. -/
private theorem rk_energy_sub_le_sq_norm_residual {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}
    (hh : 0 ≤ h) {A Y : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = Y)
    (W : Matrix m n ℝ) :
    ‖W - A‖ ^ 2 + h * ‖B * (W - A)‖ ^ 2 + h * ‖(W - A) * Cᵀ‖ ^ 2 ≤
      ‖Y - (W + h • (Bᵀ * B * W + W * (Cᵀ * C)))‖ ^ 2 := by
  have e : Y - (W + h • (Bᵀ * B * W + W * (Cᵀ * C))) =
      -((W - A) + h • (Bᵀ * B * (W - A) + (W - A) * (Cᵀ * C))) := by
    rw [← hA]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
    abel
  rw [e, norm_neg]
  exact rk_energy_le_sq_norm B C hh (W - A)

/-- One double sweep of the factored ADI iteration: the residual of the correction
`(s + t - 1) Z S Yᵀ` is the difference of two products of factors. -/
private theorem rk_adi_sweep {M : Matrix m m ℝ} {N : Matrix n n ℝ} {h s t : ℝ}
    {Uh Z : Matrix m ι ℝ} {Vh Yv : Matrix n κ ℝ} (S : Matrix ι κ ℝ)
    (hZ : s • Z + h • (M * Z) = Uh) (hY : t • Yv + h • (Nᵀ * Yv) = Vh) :
    (s + t - 1) • (Z * S * Yvᵀ) +
        h • (M * ((s + t - 1) • (Z * S * Yvᵀ)) + (s + t - 1) • (Z * S * Yvᵀ) * N) =
      Uh * S * Vhᵀ - (Uh - (s + t - 1) • Z) * S * (Vh - (s + t - 1) • Yv)ᵀ := by
  subst hZ hY
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  module

/-- The factored ADI iteration with `k` pairs of shifts: the residual of the sum of the
corrections is the product of the last factors. -/
private theorem rk_adi_residual {M : Matrix m m ℝ} {N : Matrix n n ℝ} {h : ℝ} {s t : ℕ → ℝ}
    {Uh Z : ℕ → Matrix m ι ℝ} {Vh Yv : ℕ → Matrix n κ ℝ} (S : Matrix ι κ ℝ) (k : ℕ)
    (hZ : ∀ j < k, s j • Z j + h • (M * Z j) = Uh j)
    (hY : ∀ j < k, t j • Yv j + h • (Nᵀ * Yv j) = Vh j)
    (hUh : ∀ j < k, Uh (j + 1) = Uh j - (s j + t j - 1) • Z j)
    (hVh : ∀ j < k, Vh (j + 1) = Vh j - (s j + t j - 1) • Yv j) :
    (∑ j ∈ Finset.range k, (s j + t j - 1) • (Z j * S * (Yv j)ᵀ)) +
        h • (M * (∑ j ∈ Finset.range k, (s j + t j - 1) • (Z j * S * (Yv j)ᵀ)) +
          (∑ j ∈ Finset.range k, (s j + t j - 1) • (Z j * S * (Yv j)ᵀ)) * N) =
      Uh 0 * S * (Vh 0)ᵀ - Uh k * S * (Vh k)ᵀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun j hj => hZ j (Nat.lt_succ_of_lt hj))
      (fun j hj => hY j (Nat.lt_succ_of_lt hj)) (fun j hj => hUh j (Nat.lt_succ_of_lt hj))
      (fun j hj => hVh j (Nat.lt_succ_of_lt hj))
    have h2 := rk_adi_sweep S (hZ k (Nat.lt_succ_self k)) (hY k (Nat.lt_succ_self k))
    rw [← hUh k (Nat.lt_succ_self k), ← hVh k (Nat.lt_succ_self k)] at h2
    rw [Finset.sum_range_succ, Matrix.mul_add, Matrix.add_mul]
    rw [show ∀ a b c d e f : Matrix m n ℝ, a + b + h • (c + d + (e + f)) =
      (a + h • (c + e)) + (b + h • (d + f)) from fun a b c d e f => by module, ih', h2]
    abel

end ImplicitBUGRationalKrylov

open ImplicitBUGRationalKrylov

section Step

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {B : Matrix p m ℝ} {C : Matrix q n ℝ} {ε τ ϑ t₁ h : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ : Matrix m n ℝ}

/-- **The energy error of a step is at most every squared residual norm.** Let
`F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0` and `A + h (BᵀB A + A CᵀC) = Y₀` (backward Euler on the full
matrix). For a step of the implicit BUG integrator with any new bases `U₁`, `V₁` and every
`W = U₁ G V₁ᵀ`,

  `‖U₁ S₁ V₁ᵀ - A‖² + h ‖B (U₁ S₁ V₁ᵀ - A)‖² + h ‖(U₁ S₁ V₁ᵀ - A) Cᵀ‖² ≤
    ‖Y₀ - (W + h (BᵀB W + W CᵀC))‖²`.

The right-hand side is computable without `A`; no bound of `B`, `C` is used. -/
theorem IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_residual_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    (G : Matrix k₁ k₂ ℝ) :
    ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2 ≤
      ‖U₀ * S₀ * V₀ᵀ - (U₁ * G * V₁ᵀ +
        h • (Bᵀ * B * (U₁ * G * V₁ᵀ) + U₁ * G * V₁ᵀ * (Cᵀ * C)))‖ ^ 2 :=
  (hs.energy_sub_le_of_sylvester hh hA G).trans
    (rk_energy_sub_le_sq_norm_residual hh hA (U₁ * G * V₁ᵀ))

/-- **Bases that contain the ADI factors: the energy error is at most the ADI residual.** Let
`F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0` and `A + h (BᵀB A + A CᵀC) = Y₀`. Let `sⱼ`, `tⱼ` (`j < k`) be
shifts and let the new bases contain the factors of the ADI iteration for `A`: with `Û₀ = U₀`,
`V̂₀ = V₀`,

  `(sⱼ + h BᵀB) U₁ Rⱼ = Ûⱼ`,  `Ûⱼ₊₁ = Ûⱼ - (sⱼ + tⱼ - 1) U₁ Rⱼ`,
  `(tⱼ + h CᵀC) V₁ Tⱼ = V̂ⱼ`,  `V̂ⱼ₊₁ = V̂ⱼ - (sⱼ + tⱼ - 1) V₁ Tⱼ`.

Then the energy error of the step against `A` is at most `‖Ûₖ S₀ V̂ₖᵀ‖²`. Here
`Ûₖ = ∏ⱼ (h BᵀB + 1 - tⱼ) (h BᵀB + sⱼ)⁻¹ U₀` and `V̂ₖ = ∏ⱼ (h CᵀC + 1 - sⱼ) (h CᵀC + tⱼ)⁻¹ V₀`:
the stiffness enters only through a rational function of the shifts. -/
theorem IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_adi_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    {k : ℕ} {s t : ℕ → ℝ} {Uh : ℕ → Matrix m (Fin r) ℝ} {Vh : ℕ → Matrix n (Fin r) ℝ}
    {R : ℕ → Matrix k₁ (Fin r) ℝ} {T : ℕ → Matrix k₂ (Fin r) ℝ}
    (hU0 : Uh 0 = U₀) (hV0 : Vh 0 = V₀)
    (hR : ∀ j < k, s j • (U₁ * R j) + h • (Bᵀ * B * (U₁ * R j)) = Uh j)
    (hT : ∀ j < k, t j • (V₁ * T j) + h • (Cᵀ * C * (V₁ * T j)) = Vh j)
    (hUh : ∀ j < k, Uh (j + 1) = Uh j - (s j + t j - 1) • (U₁ * R j))
    (hVh : ∀ j < k, Vh (j + 1) = Vh j - (s j + t j - 1) • (V₁ * T j)) :
    ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2 ≤ ‖Uh k * S₀ * (Vh k)ᵀ‖ ^ 2 := by
  have hT' : ∀ j < k, t j • (V₁ * T j) + h • ((Cᵀ * C)ᵀ * (V₁ * T j)) = Vh j := fun j hj => by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hT j hj
  have hres := rk_adi_residual (M := Bᵀ * B) (N := Cᵀ * C) S₀ k hR hT' hUh hVh
  have hW : U₁ * (∑ j ∈ Finset.range k, (s j + t j - 1) • (R j * S₀ * (T j)ᵀ)) * V₁ᵀ =
      ∑ j ∈ Finset.range k, (s j + t j - 1) • (U₁ * R j * S₀ * (V₁ * T j)ᵀ) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have h1 := hs.energy_sub_le_sq_norm_residual_of_sylvester hh hA
    (∑ j ∈ Finset.range k, (s j + t j - 1) • (R j * S₀ * (T j)ᵀ))
  rw [hW, hres, hU0, hV0, sub_sub_cancel] at h1
  exact h1

/-- **One pair of shifts: resolvent bases.** Let `F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0` and
`A + h (BᵀB A + A CᵀC) = Y₀`. If the new bases contain the backward Euler steps of the old
bases, `(1 + h BᵀB) U₁ R = U₀` and `(1 + h CᵀC) V₁ T = V₀`, then the energy error of the step
against `A` is at most

  `‖(U₀ - U₁ R) S₀ (V₀ - V₁ T)ᵀ‖²`,

and `U₀ - U₁ R = h BᵀB U₁ R`, `V₀ - V₁ T = h CᵀC V₁ T`: the product of the rough parts of the
two bases, weighted by `S₀`. -/
theorem IsMatrixImplicitBUGStep.energy_sub_le_sq_norm_resolvent_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    {R : Matrix k₁ (Fin r) ℝ} {T : Matrix k₂ (Fin r) ℝ}
    (hR : U₁ * R + h • (Bᵀ * B * (U₁ * R)) = U₀)
    (hT : V₁ * T + h • (Cᵀ * C * (V₁ * T)) = V₀) :
    ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2 ≤
      ‖(U₀ - U₁ * R) * S₀ * (V₀ - V₁ * T)ᵀ‖ ^ 2 := by
  have h1 := hs.energy_sub_le_sq_norm_adi_of_sylvester hh hA (k := 1) (s := fun _ => 1)
    (t := fun _ => 1) (Uh := fun j => if j = 0 then U₀ else U₀ - U₁ * R)
    (Vh := fun j => if j = 0 then V₀ else V₀ - V₁ * T) (R := fun _ => R) (T := fun _ => T)
    (by simp) (by simp)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using hR)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using hT)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      norm_num)
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      norm_num)
  simpa using h1

end Step

section Existence

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}

/-- **A step exists for all bases.** For `F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0`, orthonormal old
bases `U₀`, `V₀` and ANY orthonormal new bases `U₁`, `V₁` (of any number of columns) there is a
step of the implicit BUG integrator without truncation: the K-, L- and S-step equations are
solvable, whatever the size of `B` and `C`. -/
theorem exists_isMatrixImplicitBUGStep_of_sylvester (B : Matrix p m ℝ) (C : Matrix q n ℝ)
    {h : ℝ} (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ}
    {V₁ : Matrix n k₂ ℝ} (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hU₁ : U₁ᵀ * U₁ = 1)
    (hV₁ : V₁ᵀ * V₁ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ) (t₁ : ℝ) :
    ∃ (K₁ : Matrix m (Fin r) ℝ) (L₁ : Matrix n (Fin r) ℝ) (S₁ : Matrix k₁ k₂ ℝ) (ε τ : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
        -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ 0 t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ (U₁ * S₁ * V₁ᵀ) := by
  obtain ⟨K, hK⟩ := exists_add_smul_sylvester_eq B (C * V₀) hh (U₀ * S₀)
  obtain ⟨L, hL⟩ := exists_add_smul_sylvester_eq C (B * U₀) hh (V₀ * S₀ᵀ)
  have eK : (-(Bᵀ * B * (K * V₀ᵀ)) - K * V₀ᵀ * (Cᵀ * C)) * V₀ =
      -(Bᵀ * B * K + K * ((C * V₀)ᵀ * (C * V₀))) := by
    simp only [Matrix.sub_mul, Matrix.neg_mul, Matrix.transpose_mul, Matrix.mul_assoc, hV₀,
      Matrix.mul_one]
    abel
  have eL : (-(Bᵀ * B * (U₀ * Lᵀ)) - U₀ * Lᵀ * (Cᵀ * C))ᵀ * U₀ =
      -(Cᵀ * C * L + L * ((B * U₀)ᵀ * (B * U₀))) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_assoc, hU₀,
      Matrix.mul_one]
    abel
  let Φ : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ :=
    { toFun := fun Z => -(Bᵀ * B * Z) - Z * (Cᵀ * C)
      map_add' := fun Z Z' => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun a Z => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_neg, RingHom.id_apply] }
  have hdiss : ∀ Z, ⟪Φ Z, Z⟫ ≤ 0 := by
    intro Z
    have e : ⟪Φ Z, Z⟫ = ⟪-(Bᵀ * B * Z) - Z * (Cᵀ * C), Z⟫ := rfl
    rw [e, inner_sub_left, inner_neg_left, rk_inner_gram_mul, rk_inner_mul_gram,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖B * Z‖, sq_nonneg ‖Z * Cᵀ‖]
  obtain ⟨S₁, hS₁⟩ := exists_eq_transpose_mul_add_smul_mul Φ hdiss hh hU₁ hV₁ (U₀ * S₀ * V₀ᵀ)
  refine ⟨K, L, S₁,
    max ‖(1 - U₁ * U₁ᵀ) * (-(Bᵀ * B * (K * V₀ᵀ)) - K * V₀ᵀ * (Cᵀ * C)) * (1 - V₀ * V₀ᵀ)‖
      ‖(1 - U₀ * U₀ᵀ) * (-(Bᵀ * B * (U₀ * Lᵀ)) - U₀ * Lᵀ * (Cᵀ * C)) * (1 - V₁ * V₁ᵀ)‖,
    max ‖(1 - U₁ * U₁ᵀ) * (K * V₀ᵀ)‖ ‖U₀ * Lᵀ * (1 - V₁ * V₁ᵀ)‖, ?_⟩
  exact
    { orthU₀ := hU₀
      orthV₀ := hV₀
      kstep := by
        rw [eK, smul_neg, ← sub_eq_add_neg]
        exact eq_sub_of_add_eq hK
      lstep := by
        rw [eL, smul_neg, ← sub_eq_add_neg]
        exact eq_sub_of_add_eq hL
      orthU₁ := hU₁
      orthV₁ := hV₁
      kcap := le_max_left _ _
      lcap := le_max_right _ _
      knormal := le_max_left _ _
      lnormal := le_max_right _ _
      sstep := hS₁
      trunc := by rw [sub_self, norm_zero] }

end Existence

section Run

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}

/-- **A run with residual bounds stays near the backward Euler run on the full matrix.** Let
`F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0`. Let `Yⱼ = Uⱼ Sⱼ Vⱼᵀ` be a run of `N` steps of the implicit BUG
integrator with any intermediate bases `U'ⱼ`, `V'ⱼ` and truncation tolerances `ϑⱼ`, and let `Xⱼ`
be the backward Euler run on the full matrix. If in step `j` some matrix `U'ⱼ Gⱼ V'ⱼᵀ` of the
intermediate bases has a residual of norm at most `δⱼ` for the backward Euler equation with the
right-hand side `Yⱼ` (for bases that contain the ADI factors: the ADI residual), then

  `‖Y_N - X_N‖ ≤ ‖Y₀ - X₀‖ + ∑ j < N, (δⱼ + ϑⱼ)`.

No bound of `B`, `C` and no lower bound of a singular value enters. -/
theorem norm_implicitBUG_run_sub_le_of_sylvester_residual {N : ℕ} {ε τ ϑ δ t : ℕ → ℝ}
    {U : ℕ → Matrix m (Fin r) ℝ} {S : ℕ → Matrix (Fin r) (Fin r) ℝ}
    {V : ℕ → Matrix n (Fin r) ℝ} {K : ℕ → Matrix m (Fin r) ℝ} {L : ℕ → Matrix n (Fin r) ℝ}
    {U' : ℕ → Matrix m k₁ ℝ} {V' : ℕ → Matrix n k₂ ℝ} {S' G : ℕ → Matrix k₁ k₂ ℝ}
    {X : ℕ → Matrix m n ℝ}
    (hstep : ∀ j < N, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) (ε j) (τ j) (ϑ j) (t j) h (U j) (S j) (V j) (K j) (L j)
      (U' j) (V' j) (S' j) (U (j + 1) * S (j + 1) * (V (j + 1))ᵀ))
    (hh : 0 ≤ h)
    (hX : ∀ j < N, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j)
    (hres : ∀ j < N, ‖U j * S j * (V j)ᵀ - (U' j * G j * (V' j)ᵀ +
      h • (Bᵀ * B * (U' j * G j * (V' j)ᵀ) + U' j * G j * (V' j)ᵀ * (Cᵀ * C)))‖ ≤ δ j) :
    ‖U N * S N * (V N)ᵀ - X N‖ ≤
      ‖U 0 * S 0 * (V 0)ᵀ - X 0‖ + ∑ j ∈ Finset.range N, (δ j + ϑ j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      (fun j hj => hX j (Nat.lt_succ_of_lt hj)) (fun j hj => hres j (Nat.lt_succ_of_lt hj))
    have hs := hstep N (Nat.lt_succ_self N)
    obtain ⟨A, hA⟩ := exists_add_smul_sylvester_eq B C hh (U N * S N * (V N)ᵀ)
    have h1 := hs.energy_sub_le_sq_norm_residual_of_sylvester hh hA (G N)
    have h2 := hres N (Nat.lt_succ_self N)
    have h3 : ‖U' N * S' N * (V' N)ᵀ - A‖ ≤ δ N := by
      have a1 := mul_nonneg hh (sq_nonneg ‖B * (U' N * S' N * (V' N)ᵀ - A)‖)
      have a2 := mul_nonneg hh (sq_nonneg ‖(U' N * S' N * (V' N)ᵀ - A) * Cᵀ‖)
      have a3 := norm_nonneg (U N * S N * (V N)ᵀ - (U' N * G N * (V' N)ᵀ +
        h • (Bᵀ * B * (U' N * G N * (V' N)ᵀ) + U' N * G N * (V' N)ᵀ * (Cᵀ * C))))
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_self_lt_mul_self a3 (lt_of_le_of_lt h2 hc)]
    have h4 : ‖A - X (N + 1)‖ ≤ ‖U N * S N * (V N)ᵀ - X N‖ := by
      refine rk_norm_le_of_resolvent (B := B) (C := C) hh ?_
      rw [← hA, ← hX N (Nat.lt_succ_self N)]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
      abel
    have h5 := hs.trunc
    rw [Finset.sum_range_succ]
    calc ‖U (N + 1) * S (N + 1) * (V (N + 1))ᵀ - X (N + 1)‖
        = ‖(U (N + 1) * S (N + 1) * (V (N + 1))ᵀ - U' N * S' N * (V' N)ᵀ) +
            (U' N * S' N * (V' N)ᵀ - A) + (A - X (N + 1))‖ := by
          congr 1
          abel
      _ ≤ ‖U (N + 1) * S (N + 1) * (V (N + 1))ᵀ - U' N * S' N * (V' N)ᵀ‖ +
            ‖U' N * S' N * (V' N)ᵀ - A‖ + ‖A - X (N + 1)‖ := norm_add₃_le
      _ ≤ _ := by linarith

/-- The hypotheses of `norm_implicitBUG_run_sub_le_of_sylvester_residual` hold for every number
of steps, all sizes of `B`, `C` and every `h ≥ 0`: the run with the new bases equal to the old
ones, with `G = 0` (the residual is then `Yⱼ` itself). -/
example (hh : 0 ≤ h) {U₀ : Matrix m (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (S₀ : Matrix (Fin r) (Fin r) ℝ)
    (X₀ : Matrix m n ℝ) :
    ∃ (S : ℕ → Matrix (Fin r) (Fin r) ℝ) (X : ℕ → Matrix m n ℝ), S 0 = S₀ ∧ X 0 = X₀ ∧
      (∀ j, X (j + 1) + h • (Bᵀ * B * X (j + 1) + X (j + 1) * (Cᵀ * C)) = X j) ∧
      ∀ N, ‖U₀ * S N * V₀ᵀ - X N‖ ≤
        ‖U₀ * S 0 * V₀ᵀ - X 0‖ + ∑ j ∈ Finset.range N, (‖U₀ * S j * V₀ᵀ‖ + 0) := by
  choose K L S₁ ε τ hstep using fun S : Matrix (Fin r) (Fin r) ℝ =>
    exists_isMatrixImplicitBUGStep_of_sylvester B C hh hU₀ hV₀ hU₀ hV₀ S 0
  choose Rf hRf using fun Y : Matrix m n ℝ => exists_add_smul_sylvester_eq B C hh Y
  have hX : ∀ j, Rf^[j + 1] X₀ + h • (Bᵀ * B * Rf^[j + 1] X₀ + Rf^[j + 1] X₀ * (Cᵀ * C)) =
      Rf^[j] X₀ := fun j => by
    rw [Function.iterate_succ_apply']
    exact hRf _
  have hst : ∀ j, IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) (ε (S₁^[j] S₀)) (τ (S₁^[j] S₀)) 0 0 h U₀ (S₁^[j] S₀) V₀
      (K (S₁^[j] S₀)) (L (S₁^[j] S₀)) U₀ V₀ (S₁ (S₁^[j] S₀)) (U₀ * S₁^[j + 1] S₀ * V₀ᵀ) :=
    fun j => by
      rw [Function.iterate_succ_apply']
      exact hstep _
  refine ⟨fun j => S₁^[j] S₀, fun j => Rf^[j] X₀, rfl, rfl, hX, fun N => ?_⟩
  exact norm_implicitBUG_run_sub_le_of_sylvester_residual (B := B) (C := C) (N := N)
    (ε := fun j => ε (S₁^[j] S₀)) (τ := fun j => τ (S₁^[j] S₀)) (ϑ := fun _ => 0)
    (δ := fun j => ‖U₀ * S₁^[j] S₀ * V₀ᵀ‖) (t := fun _ => 0) (U := fun _ => U₀)
    (S := fun j => S₁^[j] S₀) (V := fun _ => V₀) (K := fun j => K (S₁^[j] S₀))
    (L := fun j => L (S₁^[j] S₀)) (U' := fun _ => U₀) (V' := fun _ => V₀)
    (S' := fun j => S₁ (S₁^[j] S₀)) (G := fun _ => 0) (X := fun j => Rf^[j] X₀)
    (fun j _ => hst j) hh (fun j _ => hX j) (fun j _ => by simp)

end Run

namespace RationalKrylovExample

/-- The stiff matrix `diag(0, -μ, -3μ)` acting on the columns. -/
local notation "Mᵣ" μ => (!![0, 0, 0; 0, -μ, 0; 0, 0, -(3 * μ)] : Matrix (Fin 3) (Fin 3) ℝ)

/-- The stiff matrix `diag(0, -lam)` acting on the rows. -/
local notation "Nᵣ" lam => (!![0, 0; 0, -lam] : Matrix (Fin 2) (Fin 2) ℝ)

/-- The stationary solution `e₁ e₁ᵀ`. -/
local notation "Xᵣ" => (!![1, 0; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ)

/-- A square root of `-M`: `diag(0, √μ, √(3μ))`. -/
local notation "Bᵣ" μ => (!![0, 0, 0; 0, √μ, 0; 0, 0, √(3 * μ)] : Matrix (Fin 3) (Fin 3) ℝ)

/-- A factor of `-N`: the row `(0, √lam)`. -/
local notation "Cᵣ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

private theorem gram_col {μ : ℝ} (hμ0 : 0 ≤ μ) : (Bᵣ μ)ᵀ * (Bᵣ μ) = -(Mᵣ μ) := by
  have h3 := Real.mul_self_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hμ0)
  generalize √(3 * μ) = β at h3 ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Real.mul_self_sqrt hμ0, h3]

private theorem gram_row {lam : ℝ} (hlam : 0 ≤ lam) : (Cᵣ lam)ᵀ * (Cᵣ lam) = -(Nᵣ lam) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam]

private theorem pos_and_le_one {a x : ℝ} (hx : 0 ≤ x) (ha : a * (1 + x) = 1) :
    0 < a ∧ a ≤ 1 := by
  have h1 : 0 < a := (pos_iff_pos_of_mul_pos (by rw [ha]; exact one_pos)).2 (by linarith)
  exact ⟨h1, by nlinarith [mul_nonneg h1.le hx]⟩

private theorem sub_mul_sq_le {s a : ℝ} (ha : 0 < a ∧ a ≤ 1) : (s - s * a) ^ 2 ≤ s ^ 2 := by
  have e : (1 - a) ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  nlinarith [mul_le_mul_of_nonneg_left e (sq_nonneg s)]

/-- The normalised backward Euler step of the old column basis. -/
private theorem exists_col_basis {h μ c s a b : ℝ} (hμ0 : 0 ≤ μ) (ha : a * (1 + h * μ) = 1)
    (hb : b * (1 + 3 * (h * μ)) = 1) (hw : 0 < c ^ 2 + (s * a) ^ 2 + (s * b) ^ 2) :
    ∃ (U₁ : Matrix (Fin 3) (Fin 1) ℝ) (ρ : ℝ), U₁ᵀ * U₁ = 1 ∧
      U₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) = !![c; s * a; s * b] ∧
      U₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) +
        h • ((Bᵣ μ)ᵀ * (Bᵣ μ) * (U₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ))) = !![c; s; s] := by
  have hB := gram_col hμ0
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = c ^ 2 + (s * a) ^ 2 + (s * b) ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hw, Real.sq_sqrt hw.le⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν * ρ = 1 := ⟨_, inv_mul_cancel₀ hρ0.ne'⟩
  have hUR : (!![c * ν; s * a * ν; s * b * ν] : Matrix (Fin 3) (Fin 1) ℝ) *
      (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) = !![c; s * a; s * b] := by
    ext i j
    fin_cases j
    fin_cases i
    · simp [Matrix.mul_apply]
      linear_combination c * hν
    · simp [Matrix.mul_apply]
      linear_combination s * a * hν
    · simp [Matrix.mul_apply]
      linear_combination s * b * hν
  refine ⟨!![c * ν; s * a * ν; s * b * ν], ρ, ?_, hUR, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (-(ν ^ 2)) * hρ + (ν * ρ + 1) * hν
  · rw [hUR, hB]
    ext i j
    fin_cases j
    fin_cases i
    · simp
    · simp
      linear_combination s * ha
    · simp
      linear_combination s * hb

/-- The normalised backward Euler step of the old row basis. -/
private theorem exists_row_basis {h lam c' t d : ℝ} (hlam : 0 ≤ lam)
    (hd : d * (1 + h * lam) = 1) (hw : 0 < c' ^ 2 + (t * d) ^ 2) :
    ∃ (V₁ : Matrix (Fin 2) (Fin 1) ℝ) (ρ : ℝ), V₁ᵀ * V₁ = 1 ∧
      V₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) = !![c'; t * d] ∧
      V₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) +
        h • ((Cᵣ lam)ᵀ * (Cᵣ lam) * (V₁ * (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ))) = !![c'; t] := by
  have hC := gram_row hlam
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = c' ^ 2 + (t * d) ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hw, Real.sq_sqrt hw.le⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν * ρ = 1 := ⟨_, inv_mul_cancel₀ hρ0.ne'⟩
  have hVT : (!![c' * ν; t * d * ν] : Matrix (Fin 2) (Fin 1) ℝ) *
      (!![ρ] : Matrix (Fin 1) (Fin 1) ℝ) = !![c'; t * d] := by
    ext i j
    fin_cases j
    fin_cases i
    · simp [Matrix.mul_apply]
      linear_combination c' * hν
    · simp [Matrix.mul_apply]
      linear_combination t * d * hν
  refine ⟨!![c' * ν; t * d * ν], ρ, ?_, hVT, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(ν ^ 2)) * hρ + (ν * ρ + 1) * hν
  · rw [hVT, hC]
    ext i j
    fin_cases j
    fin_cases i
    · simp
    · simp
      linear_combination t * hd

/-- The product of the rough parts of the two start bases. -/
private theorem sq_norm_rough_le {c s c' t a b d : ℝ} (ha : 0 < a ∧ a ≤ 1) (hb : 0 < b ∧ b ≤ 1)
    (hd : 0 < d ∧ d ≤ 1) :
    ‖((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) - !![c; s * a; s * b]) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      ((!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ) - !![c'; t * d])ᵀ‖ ^ 2 ≤ 2 * (s * t) ^ 2 := by
  have hN : ‖((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) - !![c; s * a; s * b]) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      ((!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ) - !![c'; t * d])ᵀ‖ ^ 2 =
      (s - s * a) ^ 2 * (t - t * d) ^ 2 + (s - s * b) ^ 2 * (t - t * d) ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
    ring
  have e1 := mul_le_mul (sub_mul_sq_le (s := s) ha) (sub_mul_sq_le (s := t) hd)
    (sq_nonneg _) (sq_nonneg _)
  have e2 := mul_le_mul (sub_mul_sq_le (s := s) hb) (sub_mul_sq_le (s := t) hd)
    (sq_nonneg _) (sq_nonneg _)
  have e3 : (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
  rw [hN, e3]
  linarith

/-- The reference is a fixed point of the backward Euler step on the full matrix. -/
private theorem resolvent_stationary {μ lam : ℝ} (hμ0 : 0 ≤ μ) (hlam : 0 ≤ lam) (h : ℝ) :
    Xᵣ + h • ((Bᵣ μ)ᵀ * (Bᵣ μ) * Xᵣ + Xᵣ * ((Cᵣ lam)ᵀ * (Cᵣ lam))) = Xᵣ := by
  rw [gram_col hμ0, gram_row hlam]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The resolvent bases repair the loss of the augmented integrator.** In the `3 × 2` family
`F(Z) = M Z + Z N`, `M = diag(0, -μ, -3μ)`, `N = diag(0, -lam)`, `Y₀ = (c, s, s)ᵀ (c', t)`,
`X = e₁ e₁ᵀ` (stationary) of `StiffAugmentedExample`, for every `h`, `μ`, `lam ≥ 0` there is a
step of the implicit BUG integrator whose new bases are the normalised backward Euler steps
`(1 - h M)⁻¹ U₀` and `(1 - h N)⁻¹ V₀` of the old bases (one column each: the cost of the K- and
L-step), and its result satisfies

  `‖U₁ S₁ V₁ᵀ - X‖ ≤ ‖Y₀ - X‖ + 2 |s t|`,

whereas every step with the column basis in the span of `U₀` and `K₁` is at distance `≥ 1/3`
from `X` when `h μ = 1 + h lam t²`, `4 s² h μ ≥ 31`
(`StiffAugmentedExample.one_div_three_le_norm_sub`). -/
theorem exists_isMatrixImplicitBUGStep_norm_sub_le {h lam μ c s c' t : ℝ} (hh : 0 ≤ h)
    (hlam : 0 ≤ lam) (hμ0 : 0 ≤ μ) (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hcs : c ^ 2 + 2 * s ^ 2 = 1)
    (hct : c' ^ 2 + t ^ 2 = 1) (t₁ : ℝ) :
    ∃ (U₁ : Matrix (Fin 3) (Fin 1) ℝ) (V₁ : Matrix (Fin 2) (Fin 1) ℝ)
      (K₁ : Matrix (Fin 3) (Fin 1) ℝ) (L₁ : Matrix (Fin 2) (Fin 1) ℝ)
      (S₁ : Matrix (Fin 1) (Fin 1) ℝ) (ε τ : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 3) (Fin 2) ℝ) =>
        (Mᵣ μ) * Z + Z * Nᵣ lam) ε τ 0 t₁ h !![c; s; s] 1 !![c'; t] K₁ L₁ U₁ V₁ S₁
        (U₁ * S₁ * V₁ᵀ) ∧
      ‖U₁ * S₁ * V₁ᵀ - Xᵣ‖ ≤
        ‖(!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) *
          (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - Xᵣ‖ + 2 * |s * t| := by
  have hB := gram_col hμ0
  have hC := gram_row hlam
  have hhμ : 0 ≤ h * μ := mul_nonneg hh hμ0
  have hhl : 0 ≤ h * lam := mul_nonneg hh hlam
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a * (1 + h * μ) = 1 := ⟨_, inv_mul_cancel₀ (by positivity)⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b * (1 + 3 * (h * μ)) = 1 := ⟨_, inv_mul_cancel₀ (by positivity)⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d * (1 + h * lam) = 1 := ⟨_, inv_mul_cancel₀ (by positivity)⟩
  have ha1 := pos_and_le_one hhμ ha
  have hb1 := pos_and_le_one (by positivity : (0 : ℝ) ≤ 3 * (h * μ)) hb
  have hd1 := pos_and_le_one hhl hd
  have ha0 := ha1.1
  have hd0 := hd1.1
  have hw : 0 < c ^ 2 + (s * a) ^ 2 + (s * b) ^ 2 := by positivity
  have hw' : 0 < c' ^ 2 + (t * d) ^ 2 := by positivity
  obtain ⟨U₁, ρ, hU₁, hUR, hR⟩ := exists_col_basis (c := c) (s := s) hμ0 ha hb hw
  obtain ⟨V₁, ρ', hV₁, hVT, hT⟩ := exists_row_basis (c' := c') (t := t) hlam hd hw'
  have hU₀ : (!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ * !![c; s; s] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination hcs
  have hV₀ : (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ * !![c'; t] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hct
  obtain ⟨K₁, L₁, S₁, ε, τ, hs⟩ := exists_isMatrixImplicitBUGStep_of_sylvester (Bᵣ μ) (Cᵣ lam) hh
    hU₀ hV₀ hU₁ hV₁ 1 t₁
  obtain ⟨A, hA⟩ := exists_add_smul_sylvester_eq (Bᵣ μ) (Cᵣ lam) hh
    ((!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c'; t]ᵀ)
  have h1 := hs.energy_sub_le_sq_norm_resolvent_of_sylvester hh hA hR hT
  rw [hUR, hVT] at h1
  have h2 := sq_norm_rough_le (c := c) (s := s) (c' := c') (t := t) ha1 hb1 hd1
  have h6 : ‖U₁ * S₁ * V₁ᵀ - A‖ ≤ 2 * |s * t| := by
    have a1 := mul_nonneg hh (sq_nonneg ‖(Bᵣ μ) * (U₁ * S₁ * V₁ᵀ - A)‖)
    have a2 := mul_nonneg hh (sq_nonneg ‖(U₁ * S₁ * V₁ᵀ - A) * (Cᵣ lam)ᵀ‖)
    have a3 : ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 ≤ 2 * (s * t) ^ 2 := by linarith
    have a4 : (2 * |s * t|) ^ 2 = 4 * (s * t) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 2 * |s * t|) hc,
      sq_nonneg (s * t)]
  have hX0 := resolvent_stationary hμ0 hlam h
  have h7 : ‖A - Xᵣ‖ ≤ ‖(!![c; s; s] : Matrix (Fin 3) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![c'; t] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ - Xᵣ‖ := by
    refine rk_norm_le_of_resolvent (B := Bᵣ μ) (C := Cᵣ lam) hh ?_
    have e : (A - Xᵣ) + h • ((Bᵣ μ)ᵀ * (Bᵣ μ) * (A - Xᵣ) + (A - Xᵣ) * ((Cᵣ lam)ᵀ * (Cᵣ lam))) =
        (A + h • ((Bᵣ μ)ᵀ * (Bᵣ μ) * A + A * ((Cᵣ lam)ᵀ * (Cᵣ lam)))) -
          (Xᵣ + h • ((Bᵣ μ)ᵀ * (Bᵣ μ) * Xᵣ + Xᵣ * ((Cᵣ lam)ᵀ * (Cᵣ lam)))) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_add]
      abel
    rw [e, hA, hX0]
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 3) (Fin 2) ℝ) =>
      -((Bᵣ μ)ᵀ * (Bᵣ μ) * Z) - Z * ((Cᵣ lam)ᵀ * (Cᵣ lam))) = fun _ Z =>
      (Mᵣ μ) * Z + Z * Nᵣ lam := by
    funext _ Z
    rw [hB, hC, Matrix.neg_mul, neg_neg, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  refine ⟨U₁, V₁, K₁, L₁, S₁, ε, τ, hs, ?_⟩
  calc ‖U₁ * S₁ * V₁ᵀ - Xᵣ‖ = ‖(U₁ * S₁ * V₁ᵀ - A) + (A - Xᵣ)‖ := by
        congr 1
        abel
    _ ≤ ‖U₁ * S₁ * V₁ᵀ - A‖ + ‖A - Xᵣ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end RationalKrylovExample

end LeanDLRA

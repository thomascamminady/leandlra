import LeanDLRA.Research.ImplicitBUGStiffLemmas

/-!
# The implicit BUG integrator with a stiff row operator: the local error

Let `F(Z) = M Z - Z CᵀC` with `M` dissipative and bounded by `μ` and `C` arbitrary. This file
compares one step of the BUG integrator with backward Euler substeps with the backward Euler
step `Ỹ` of the full problem FROM THE SAME START VALUE, `Ỹ - h M Ỹ + h Ỹ CᵀC = Y₀`. The difference
`Y₁ - Ỹ` (the local error) depends on the start value only, and it is bounded by `h μ` times the
stiff energy of the start value minus a free comparison matrix: no term of the size of the start
value or of an error enters, and there is no restriction on `h μ`.

## Main results

* `ImplicitBUGStiffLocal.sq_norm_add_le_of_backwardEuler`: a backward Euler step of the full
  problem satisfies `‖W‖² + 2 h ‖W Cᵀ‖² ≤ ‖R‖²`.
* `ImplicitBUGStiffLocal.exists_backwardEuler`: the backward Euler step exists.
* `ImplicitBUGStiffLocal.norm_smul_mul_gram_le`: the stiff term `h W CᵀC` of a (Galerkin)
  backward Euler step is bounded by the start value and by the stiff energy of the start value
  minus any comparison matrix.
* `ImplicitBUGStiffLocal.sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors` and
  `IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester`: the local
  error bound `√(‖Y₁ - Ỹ‖² + 2 h ‖(Y₁ - Ỹ) Cᵀ‖²) ≤ (27/4 + 2 h μ) h μ λ`, where
  `λ = min(‖Y₀‖, √h ‖(Y₀ - Z) Cᵀ‖ / 2 + h ‖Z CᵀC‖)` for every matrix `Z`.
* `ImplicitBUGStiffLocal.exists_sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors` and
  `IsMatrixImplicitBUGStep.exists_sqrt_sq_norm_galerkin_sub_backwardEuler_add_le`: the local error
  is bounded by two quantities of the step itself, the stiff source `h (Ξ - P₁) Y_L CᵀC` of the
  S-step and the normal part `h (1 - P₁) M (Y_K - Y₁)` of the K-step.

## Implementation notes

With the Galerkin resolvent `Ξ` of the new column space and `D = Y₁ - Ξ Y_L`, the residual of the
step in the backward Euler equation of the full problem is

  `Y₁ - h M Y₁ + h Y₁ CᵀC - Y₀ = D - h P₁ M D + h (1 - P₁) M (Y_K - Y₁) + h D CᵀC`
  `    + h (Ξ - P₁) Y_L CᵀC`.

The equation of `Y₁ - Ỹ` is tested with `Y₁ - Ỹ`. The part of `Y₁ - Ỹ` outside the new column
space is the part of `Y_K - Ỹ` outside it, so that the normal part of the K-step costs
`h μ ‖Y_K - Ỹ‖` and no restriction on `h μ` is needed.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA

open ImplicitBUGStiffLemmas

namespace ImplicitBUGStiffLocal

section Lemmas

variable {m n k p : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p]

/-- An orthogonal projector splits the square of the Frobenius norm. -/
theorem sq_norm_proj_mul_add {P : Matrix m m ℝ} (hP : P * P = P) (hPt : Pᵀ = P)
    (A : Matrix m p ℝ) : ‖P * A‖ ^ 2 + ‖A - P * A‖ ^ 2 = ‖A‖ ^ 2 := by
  have hz : ⟪P * A, A - P * A⟫ = 0 := by
    rw [inner_proj_mul hPt, Matrix.mul_sub, ← Matrix.mul_assoc, hP, sub_self, inner_zero_right]
  have h1 := norm_add_sq_real (P * A) (A - P * A)
  rw [add_sub_cancel, hz] at h1
  linarith

/-- **Energy identity of a backward Euler step of the full problem**: if
`W - h M W + h W CᵀC = R` with `M` dissipative, then `‖W‖² + 2 h ‖W Cᵀ‖² ≤ ‖R‖²`. -/
theorem sq_norm_add_le_of_backwardEuler {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) {W R : Matrix m n ℝ}
    (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    ‖W‖ ^ 2 + 2 * (h * ‖W * Cᵀ‖ ^ 2) ≤ ‖R‖ ^ 2 := by
  have h1 : ⟪W, W⟫ - h * ⟪M * W, W⟫ + h * ⟪W * Cᵀ, W * Cᵀ⟫ = ⟪R, W⟫ := by
    have h0 := congrArg (fun X => ⟪X, W⟫) heq
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at h0
    rwa [← Matrix.mul_assoc W, Frobenius.inner_mul_right (W * Cᵀ) C W] at h0
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  nlinarith [real_inner_le_norm R W, sq_nonneg (‖R‖ - ‖W‖),
    mul_nonpos_of_nonneg_of_nonpos hh (inner_mul_self_nonpos hdiss W)]

/-- A backward Euler step of the full problem does not increase the Frobenius norm, measured
after the step together with twice the stiff energy. -/
theorem sqrt_sq_norm_add_le_of_backwardEuler {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) {W R : Matrix m n ℝ}
    (heq : W - h • (M * W) + h • (W * (Cᵀ * C)) = R) :
    √(‖W‖ ^ 2 + 2 * (h * ‖W * Cᵀ‖ ^ 2)) ≤ ‖R‖ :=
  Real.sqrt_le_iff.2 ⟨norm_nonneg R, sq_norm_add_le_of_backwardEuler hdiss hh heq⟩

/-- **The backward Euler step of the full problem exists**: for a dissipative `M` and `h ≥ 0`
the equation `W - h M W + h W CᵀC = R` has a solution. -/
theorem exists_backwardEuler {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h : ℝ}
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 ≤ h) (R : Matrix m n ℝ) :
    ∃ W : Matrix m n ℝ, W - h • (M * W) + h • (W * (Cᵀ * C)) = R := by
  let L : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ :=
    { toFun := fun W => W - h • (M * W) + h • (W * (Cᵀ * C))
      map_add' := fun A B => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add, smul_sub,
          smul_comm c h] }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun W hW => ?_
    have h0 : W - h • (M * W) + h • (W * (Cᵀ * C)) = 0 := hW
    have := norm_le_of_backwardEuler hdiss hh h0
    rw [norm_zero] at this
    exact norm_le_zero_iff.1 this
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective.1 hinj) R
  exact ⟨W, hW⟩

variable {M : Matrix m m ℝ} {C : Matrix k n ℝ} {h μ : ℝ} {P₀ P₁ : Matrix m m ℝ}
  {Q₀ Q₁ : Matrix n n ℝ} {Y₀ YK YL Y₁ Yt : Matrix m n ℝ}

/-- **The stiff term of a Galerkin backward Euler step.** If `W = P W` and
`W - h P M W + h W CᵀC = R` for an orthogonal projector `P` (the L-step for the old column
projector, the backward Euler step of the full problem for `P = 1`), then the stiff term
`h W CᵀC` is bounded by `‖R‖`, and for every matrix `Z` by half the square root of the stiff
energy of `R - Z` plus `h ‖Z CᵀC‖`. -/
theorem norm_smul_mul_gram_le {P : Matrix m m ℝ} (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hPt : Pᵀ = P) (hh : 0 < h) {W R : Matrix m n ℝ} (hW : P * W = W)
    (heq : W - h • (P * (M * W)) + h • (W * (Cᵀ * C)) = R) :
    ‖h • (W * (Cᵀ * C))‖ ≤ ‖R‖ ∧ ∀ Z : Matrix m n ℝ,
      ‖h • (W * (Cᵀ * C))‖ ≤ √h * ‖(R - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖ := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = h • (W * (Cᵀ * C)) := ⟨_, rfl⟩
  rw [← hΛ]
  have hPΛ : P * Λ = Λ := by rw [hΛ, Matrix.mul_smul, ← Matrix.mul_assoc, hW]
  have gram : ∀ A B : Matrix m n ℝ, ⟪A * (Cᵀ * C), B⟫ = ⟪A * Cᵀ, B * Cᵀ⟫ := fun A B => by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]
  have gram' : ∀ A B : Matrix m n ℝ, ⟪A, B * (Cᵀ * C)⟫ = ⟪A * Cᵀ, B * Cᵀ⟫ := fun A B => by
    rw [real_inner_comm, gram, real_inner_comm]
  constructor
  · have hI : ⟪W, Λ⟫ - h * ⟪P * (M * W), Λ⟫ + ⟪Λ, Λ⟫ = ⟪R, Λ⟫ := by
      have heq' := heq
      rw [← hΛ] at heq'
      have h0 := congrArg (fun A => ⟪A, Λ⟫) heq'
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at h0
      exact h0
    have hWΛ : ⟪W, Λ⟫ = h * ‖W * Cᵀ‖ ^ 2 := by
      rw [hΛ, real_inner_smul_right, gram', real_inner_self_eq_norm_sq]
    have hMW : ⟪P * (M * W), Λ⟫ = h * ⟪M * (W * Cᵀ), W * Cᵀ⟫ := by
      rw [inner_proj_mul hPt, hPΛ, hΛ, real_inner_smul_right, gram', Matrix.mul_assoc]
    have hi := inner_mul_self_nonpos hdiss (W * Cᵀ)
    have hl := real_inner_le_norm R Λ
    have hhh : 0 ≤ -(h * (h * ⟪M * (W * Cᵀ), W * Cᵀ⟫)) := by
      have := mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hi)
      linarith
    rw [real_inner_self_eq_norm_sq, hWΛ, hMW] at hI
    refine le_of_sq_le_mul (norm_nonneg _) ?_
    nlinarith [mul_nonneg hh.le (sq_nonneg ‖W * Cᵀ‖)]
  · intro Z
    have eΛ : Λ - h • (P * (M * Λ)) + h • (Λ * (Cᵀ * C)) = h • (R * (Cᵀ * C)) := by
      have := congrArg (fun A => h • (A * (Cᵀ * C))) heq
      simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub, smul_add] at this
      rw [← this, hΛ]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have hJ : ⟪Λ, Λ⟫ - h * ⟪M * Λ, Λ⟫ + h * ⟪Λ * Cᵀ, Λ * Cᵀ⟫ =
        h * (⟪(R - Z) * Cᵀ, Λ * Cᵀ⟫ + ⟪Z * (Cᵀ * C), Λ⟫) := by
      have h0 := congrArg (fun A => ⟪A, Λ⟫) eΛ
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at h0
      rw [inner_proj_mul hPt, hPΛ, gram, gram] at h0
      rw [h0, gram, ← inner_add_left, ← Matrix.add_mul, sub_add_cancel]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hJ
    have hMΛ := inner_mul_self_nonpos hdiss Λ
    have g1 := real_inner_le_norm ((R - Z) * Cᵀ) (Λ * Cᵀ)
    have g2 := real_inner_le_norm (Z * (Cᵀ * C)) Λ
    have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
    refine le_half_add_of_sq_add_sq_le (c := √h * ‖Λ * Cᵀ‖)
      (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg _)) (mul_nonneg hh.le (norm_nonneg _)) ?_
    rw [mul_pow, hs2, sqrt_mul_mul_sqrt_mul hh.le]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh.le hMΛ, mul_le_mul_of_nonneg_left g1 hh.le,
      mul_le_mul_of_nonneg_left g2 hh.le]

/-- The stiff term of the backward Euler step of the full problem. -/
theorem norm_smul_backwardEuler_mul_gram_le
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) :
    ‖h • (Yt * (Cᵀ * C))‖ ≤ ‖Y₀‖ ∧ ∀ Z : Matrix m n ℝ,
      ‖h • (Yt * (Cᵀ * C))‖ ≤ √h * ‖(Y₀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖ := by
  classical
  exact norm_smul_mul_gram_le (P := 1) hdiss Matrix.transpose_one hh (Matrix.one_mul _)
    (by rw [Matrix.one_mul]; exact hYt)

/-- The part of the backward Euler step outside the old row space is bounded by its stiff
term. -/
theorem norm_backwardEuler_sub_mul_proj_le (hQ₀ : Q₀ * Q₀ = Q₀)
    (hQ₀t : Q₀ᵀ = Q₀) (yQ : Y₀ * Q₀ = Y₀) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) :
    ‖Yt - Yt * Q₀‖ ≤ ‖h • (Yt * (Cᵀ * C))‖ := by
  classical
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = h • (Yt * (Cᵀ * C)) := ⟨_, rfl⟩
  rw [← hΛ] at hYt ⊢
  have e1 : Yt - h • (M * Yt) = Y₀ - Λ := eq_sub_of_add_eq hYt
  have e2 : Yt * Q₀ - h • (M * (Yt * Q₀)) = Y₀ - Λ * Q₀ := by
    have := congrArg (fun A => A * Q₀) e1
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    rw [this, yQ]
  have heq : Yt - Yt * Q₀ - h • ((1 : Matrix m m ℝ) * (M * (Yt - Yt * Q₀))) =
      (1 : Matrix m m ℝ) * (-(Λ - Λ * Q₀)) := by
    rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_sub, smul_sub, sub_sub_sub_comm, e1, e2]
    abel
  have h1 := norm_le_of_galerkin hdiss Matrix.transpose_one hh.le (Matrix.one_mul _) heq
  rw [norm_neg] at h1
  exact h1.trans (norm_sub_mul_proj_le hQ₀ hQ₀t Λ)

/-- **The K-step against the backward Euler step from the same start value.** The two differ
by at most the stiff term of the K-step and twice the stiff term of the backward Euler step; the
parts inside and outside the old row space are orthogonal. -/
theorem sq_norm_kstep_sub_backwardEuler_le (hQ₀ : Q₀ * Q₀ = Q₀)
    (hQ₀t : Q₀ᵀ = Q₀) (yQ : Y₀ * Q₀ = Y₀) (kQ : YK * Q₀ = YK)
    (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hh : 0 < h) {Λ : Matrix m n ℝ}
    (eqK : YK + Λ - h • (M * YK) = Y₀)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) :
    ‖YK - Yt‖ ^ 2 ≤ (‖Λ‖ + ‖h • (Yt * (Cᵀ * C))‖) ^ 2 + ‖h • (Yt * (Cᵀ * C))‖ ^ 2 := by
  have hX : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀ + 0 := by rw [add_zero]; exact hYt
  have n1 := norm_kstep_sub_le hQ₀ hQ₀t yQ hdiss hh eqK hX
  rw [sub_zero, sub_self, norm_zero, add_zero] at n1
  have n2 := norm_backwardEuler_sub_mul_proj_le hQ₀ hQ₀t yQ hdiss hh hYt
  have hwQ : (YK - Yt * Q₀) * Q₀ = YK - Yt * Q₀ := by
    rw [Matrix.sub_mul, kQ, Matrix.mul_assoc, hQ₀]
  have hzQ : (Yt - Yt * Q₀) * Q₀ = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hQ₀, sub_self]
  have hz : ⟪YK - Yt * Q₀, Yt - Yt * Q₀⟫ = 0 := by
    rw [← hwQ, inner_mul_proj hQ₀t, hzQ, inner_zero_right]
  have e : YK - Yt = YK - Yt * Q₀ - (Yt - Yt * Q₀) := by abel
  have h1 := norm_sub_sq_real (YK - Yt * Q₀) (Yt - Yt * Q₀)
  rw [← e, hz] at h1
  have a1 : ‖YK - Yt * Q₀‖ ^ 2 ≤ (‖Λ‖ + h * ‖Yt * (Cᵀ * C)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have a2 : ‖Yt - Yt * Q₀‖ ^ 2 ≤ ‖h • (Yt * (Cᵀ * C))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) n2 2
  have e3 : ‖h • (Yt * (Cᵀ * C))‖ = h * ‖Yt * (Cᵀ * C)‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh.le]
  rw [e3] at a2 ⊢
  linarith

/-- **The normal part of the K-step, tested with the local error.** The part of `Y₁ - Ỹ` outside
the new column space is the part of `Y_K - Ỹ` outside it, so that
`⟪(1 - P₁) M (Y_K - Y₁), Y₁ - Ỹ⟫ ≤ μ ‖Y_K - Ỹ‖ ‖Y₁ - Ỹ‖`. -/
theorem inner_sub_proj_mul_le (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (kP : P₁ * YK = YK)
    (sP : P₁ * Y₁ = Y₁) :
    ⟪M * (YK - Y₁) - P₁ * (M * (YK - Y₁)), Y₁ - Yt⟫ ≤ μ * ‖YK - Yt‖ * ‖Y₁ - Yt‖ := by
  obtain ⟨G, hG⟩ : ∃ G, G = YK - Yt := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = Y₁ - Yt := ⟨_, rfl⟩
  rw [← hG, ← he]
  have eA : YK - Y₁ = P₁ * G - P₁ * e := by
    rw [hG, he, Matrix.mul_sub, Matrix.mul_sub, kP, sP]; abel
  have ec : e - P₁ * e = G - P₁ * G := by
    rw [hG, he, Matrix.mul_sub, Matrix.mul_sub, kP, sP]; abel
  have h1 : ⟪M * (YK - Y₁) - P₁ * (M * (YK - Y₁)), e⟫ = ⟪M * (YK - Y₁), e - P₁ * e⟫ := by
    rw [inner_sub_left, inner_proj_mul hP₁t, inner_sub_right]
  have n1 : ‖M * (YK - Y₁)‖ ≤ μ * (‖P₁ * G‖ + ‖P₁ * e‖) := by
    refine (norm_mul_le_mul_norm hμ0 hμ _).trans (mul_le_mul_of_nonneg_left ?_ hμ0)
    rw [eA]; exact norm_sub_le _ _
  have n2 := (real_inner_le_norm (M * (YK - Y₁)) (e - P₁ * e)).trans
    (mul_le_mul_of_nonneg_right n1 (norm_nonneg _))
  have cs := mul_add_mul_le_sqrt_mul_sqrt (norm_nonneg (P₁ * G)) (norm_nonneg (G - P₁ * G))
    (norm_nonneg (e - P₁ * e)) (norm_nonneg (P₁ * e))
  have pG := sq_norm_proj_mul_add hP₁ hP₁t G
  have pe := sq_norm_proj_mul_add hP₁ hP₁t e
  rw [pG, add_comm (‖e - P₁ * e‖ ^ 2), pe, Real.sqrt_sq (norm_nonneg G),
    Real.sqrt_sq (norm_nonneg e)] at cs
  rw [h1]
  have e2 : μ * (‖P₁ * G‖ + ‖P₁ * e‖) * ‖e - P₁ * e‖ =
      μ * (‖P₁ * G‖ * ‖e - P₁ * e‖ + ‖G - P₁ * G‖ * ‖P₁ * e‖) := by
    rw [← ec]; ring
  rw [e2] at n2
  have := mul_le_mul_of_nonneg_left cs hμ0
  linarith

/-- The scalar form of the local error bound with twice the stiff energy: `x`, `E` are the local
error and the square root of its stiff energy, `d`, `c` those of the S-step remainder, `s` bounds
the stiff source and `κ` the K-step against the backward Euler step. -/
theorem local_scalar {x E d c s κ η : ℝ} (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hκ : 0 ≤ κ) (hη : 0 ≤ η) (hD : d ^ 2 + c ^ 2 ≤ s * d)
    (hmain : x ^ 2 + E ^ 2 ≤ (1 + η) * d * x + c * E + s * x + η * κ * x) :
    √(x ^ 2 + 2 * E ^ 2) ≤ (9 / 4 + η) * s + η * κ := by
  have hds : d ≤ s := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [sq_nonneg c, mul_pos (lt_of_le_of_lt hs hcon) (sub_pos.2 hcon)]
  have hc2 : c ^ 2 ≤ d * (s - d) := by nlinarith
  have hcs : c ≤ s / 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have p1 : 0 < c + s / 2 := by linarith
    nlinarith [sq_nonneg (d - s / 2), mul_pos (sub_pos.2 hcon) p1]
  obtain ⟨B, hB⟩ : ∃ B, B = (1 + η) * d + s + η * κ := ⟨_, rfl⟩
  have hsB : s ≤ B := by rw [hB]; nlinarith [mul_nonneg hη hd, mul_nonneg hη hκ]
  have hB0 : 0 ≤ B := hs.trans hsB
  have h1 : x ^ 2 + E ^ 2 ≤ B * x + c * E := by
    have : B * x = (1 + η) * d * x + s * x + η * κ * x := by rw [hB]; ring
    linarith
  have e1 : E ^ 2 - c * E ≤ B ^ 2 / 4 := by nlinarith [sq_nonneg (x - B / 2)]
  have hE' : E ≤ c + B / 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have p1 : 0 < E + B / 2 := by linarith
    nlinarith [mul_pos (sub_pos.2 hcon) p1, mul_nonneg hc hB0]
  have h2 : x ^ 2 + 2 * E ^ 2 ≤ B ^ 2 + B * c + 2 * c ^ 2 := by
    nlinarith [sq_nonneg (x - B), mul_le_mul_of_nonneg_left hE' hc]
  have hT : (9 / 4 + η) * s + η * κ = B + (s / 4 + (1 + η) * (s - d)) := by rw [hB]; ring
  have h3 : B ^ 2 + B * c + 2 * c ^ 2 ≤ ((9 / 4 + η) * s + η * κ) ^ 2 := by
    rw [hT]
    nlinarith [mul_le_mul_of_nonneg_left hcs hB0, mul_nonneg (sub_nonneg.2 hds) (sub_nonneg.2 hds),
      mul_nonneg (sub_nonneg.2 hsB) (sub_nonneg.2 hds),
      mul_nonneg hB0 (mul_nonneg hη (sub_nonneg.2 hds)),
      sq_nonneg (s / 4 + (1 + η) * (s - d))]
  exact Real.sqrt_le_iff.2 ⟨by nlinarith [mul_nonneg hη hs, mul_nonneg hη hκ], h2.trans h3⟩

/-- The scalar form of the local error bound in terms of the stiff source `s` and the normal part
`r` of the K-step. -/
theorem local_scalar' {x E d c s r η : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hη : 0 ≤ η) (hD : d ^ 2 + c ^ 2 ≤ s * d)
    (hmain : x ^ 2 + E ^ 2 ≤ (1 + η) * d * x + c * E + s * x + r * x) :
    √(x ^ 2 + E ^ 2) ≤ (2 + η) * s + r := by
  have hds : d ≤ s := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [sq_nonneg c, mul_pos (lt_of_le_of_lt hs hcon) (sub_pos.2 hcon)]
  obtain ⟨B, hB⟩ : ∃ B, B = (1 + η) * d + s + r := ⟨_, rfl⟩
  have hsB : s ≤ B := by rw [hB]; nlinarith [mul_nonneg hη hd]
  have hB0 : 0 ≤ B := hs.trans hsB
  have h1 : x ^ 2 + E ^ 2 ≤ B * x + c * E := by
    have : B * x = (1 + η) * d * x + s * x + r * x := by rw [hB]; ring
    linarith
  have cs := mul_add_mul_le_sqrt_mul_sqrt hB0 hc hx hE
  have h2 : √(x ^ 2 + E ^ 2) ^ 2 ≤ √(B ^ 2 + c ^ 2) * √(x ^ 2 + E ^ 2) := by
    rw [Real.sq_sqrt (by positivity)]
    exact h1.trans cs
  refine (le_of_sq_le_mul (Real.sqrt_nonneg _) h2).trans ?_
  have hT : (2 + η) * s + r = B + (1 + η) * (s - d) := by rw [hB]; ring
  refine Real.sqrt_le_iff.2 ⟨by nlinarith [mul_nonneg hη hs], ?_⟩
  rw [hT]
  nlinarith [mul_nonneg (sub_nonneg.2 hsB) (sub_nonneg.2 hds),
    mul_nonneg hd (sub_nonneg.2 hds), mul_nonneg hB0 (mul_nonneg hη (sub_nonneg.2 hds)),
    sq_nonneg ((1 + η) * (s - d)), mul_nonneg hs (sub_nonneg.2 hds)]

/-- **The local error equation, tested.** With the Galerkin resolvent `Ξ` of the new column
space and the S-step remainder `D = Y₁ - Ξ Y_L`, the local error `Y₁ - Ỹ` against the backward
Euler step `Ỹ` of the full problem from the same start value is bounded, with its stiff energy,
by `D`, the stiff source `h (Ξ - P₁) Y_L CᵀC` and the normal part `h (1 - P₁) M (Y_K - Y₁)` of the
K-step, all tested with `Y₁ - Ỹ`. -/
theorem exists_sq_norm_sub_backwardEuler_add_le [DecidableEq m] (hP₁ : P₁ * P₁ = P₁)
    (hP₁t : P₁ᵀ = P₁) (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀) (hQ₁t : Q₁ᵀ = Q₁)
    (kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀))
    (kQ : YK * Q₀ = YK) (kP : P₁ * YK = YK)
    (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁)
    (sP : P₁ * Y₁ = Y₁) (sQ : Y₁ * Q₁ = Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) :
    ∃ (Ξ : Matrix m m ℝ) (D : Matrix m n ℝ), P₁ * Ξ = Ξ ∧
      Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M)) ∧
      ‖D‖ ^ 2 + h * ‖D * Cᵀ‖ ^ 2 ≤ -(h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), D⟫) ∧
      ‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2 ≤ (1 + h * μ) * ‖D‖ * ‖Y₁ - Yt‖ +
        √h * ‖D * Cᵀ‖ * (√h * ‖(Y₁ - Yt) * Cᵀ‖) +
        h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), Y₁ - Yt⟫ +
        h * ⟪M * (YK - Y₁) - P₁ * (M * (YK - Y₁)), Y₁ - Yt⟫ := by
  obtain ⟨Ξ, D, hΞP, hΞ, hY, hDe⟩ := exists_sstep_decomposition hP₁ hP₁t hQ₁t lEq lP lQ sEq sP
    sQ hdiss hh
  obtain ⟨Λ, eqK, hPΛ, -, -⟩ := exists_kstep_gram_term hQ₀ hQ₀t kEq kQ kP hdiss hh
  refine ⟨Ξ, D, hΞP, hΞ, hDe, ?_⟩
  obtain ⟨e, he⟩ : ∃ e, e = Y₁ - Yt := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = M * (YK - Y₁) := ⟨_, rfl⟩
  rw [← he, ← hW]
  -- the start value in terms of the substeps
  have eP : P₁ * Y₀ = Ξ * YL - h • (P₁ * (M * (Ξ * YL))) + h • (P₁ * (YL * (Cᵀ * C))) := by
    have e1 := xi_mul_sub hΞ YL
    have e2 : YL - h • (P₀ * (M * YL)) = Y₀ - h • (YL * (Cᵀ * C)) :=
      eq_sub_of_add_eq (start_eq_of_lstep lEq lP).symm
    rw [e1, e2, Matrix.mul_sub, Matrix.mul_smul]; abel
  have eC : Y₀ - P₁ * Y₀ = -(h • (M * YK) - P₁ * (h • (M * YK))) := by
    conv_lhs => rw [← eqK]
    rw [Matrix.mul_sub, Matrix.mul_add, kP, hPΛ]; abel
  have eY : Y₀ = Ξ * YL - h • (P₁ * (M * (Ξ * YL))) + h • (P₁ * (YL * (Cᵀ * C))) -
      (h • (M * YK) - P₁ * (h • (M * YK))) := by
    rw [← eP]
    calc Y₀ = P₁ * Y₀ + (Y₀ - P₁ * Y₀) := by abel
      _ = _ := by rw [eC]; abel
  -- the equation of the local error with the residual of the step
  have eρ : e - h • (M * e) + h • (e * (Cᵀ * C)) = (D - h • (P₁ * (M * D))) +
      h • (W - P₁ * W) + h • (D * (Cᵀ * C)) + h • ((Ξ - P₁) * YL * (Cᵀ * C)) := by
    have e1 : e - h • (M * e) + h • (e * (Cᵀ * C)) =
        Y₁ - h • (M * Y₁) + h • (Y₁ * (Cᵀ * C)) - Y₀ := by
      rw [he]
      conv_rhs => rw [← hYt]
      simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
      abel
    rw [e1, hW, hY]
    conv_lhs => rw [eY]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      smul_add, smul_sub, Matrix.mul_assoc]
    abel
  have hI : ⟪e, e⟫ - h * ⟪M * e, e⟫ + h * ⟪e * (Cᵀ * C), e⟫ =
      ⟪D - h • (P₁ * (M * D)), e⟫ + h * ⟪W - P₁ * W, e⟫ +
        h * ⟪D * (Cᵀ * C), e⟫ + h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), e⟫ := by
    have h0 := congrArg (fun A => ⟪A, e⟫) eρ
    rw [inner_add_left, inner_add_left, inner_add_left, inner_add_left, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left] at h0
    exact h0
  have q1 : ⟪e * (Cᵀ * C), e⟫ = ‖e * Cᵀ‖ ^ 2 := by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right, real_inner_self_eq_norm_sq]
  have q2 : ⟪D * (Cᵀ * C), e⟫ = ⟪D * Cᵀ, e * Cᵀ⟫ := by
    rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]
  rw [real_inner_self_eq_norm_sq, q1, q2] at hI
  have T3 : h * ⟪D * Cᵀ, e * Cᵀ⟫ ≤ √h * ‖D * Cᵀ‖ * (√h * ‖e * Cᵀ‖) := by
    rw [sqrt_mul_mul_sqrt_mul hh.le]
    exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hh.le
  have T1 : ⟪D - h • (P₁ * (M * D)), e⟫ ≤ (1 + h * μ) * ‖D‖ * ‖e‖ := by
    refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have n1 : ‖h • (P₁ * (M * D))‖ ≤ h * (μ * ‖D‖) := by
      rw [norm_smul, Real.norm_of_nonneg hh.le]
      exact mul_le_mul_of_nonneg_left
        ((norm_proj_mul_le hP₁ hP₁t _).trans (norm_mul_le_mul_norm hμ0 hμ D)) hh.le
    have := norm_sub_le D (h • (P₁ * (M * D)))
    linarith
  have hMe := mul_nonpos_of_nonneg_of_nonpos hh.le (inner_mul_self_nonpos hdiss e)
  linarith

/-- **The local error in terms of quantities of the step.** For a step of the BUG integrator with
backward Euler substeps (in terms of the projectors) and the backward Euler step `Ỹ` of the full
problem from the same start value, with the Galerkin resolvent `Ξ` of the new column space,

  `√(‖Y₁ - Ỹ‖² + h ‖(Y₁ - Ỹ) Cᵀ‖²) ≤ (2 + h μ) ‖h (Ξ - P₁) Y_L CᵀC‖ + ‖h (1 - P₁) M (Y_K - Y₁)‖`.

Both terms on the right are computable from the factors of the step. -/
theorem exists_sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors [DecidableEq m]
    (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁) (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀)
    (hQ₁t : Q₁ᵀ = Q₁) (kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀))
    (kQ : YK * Q₀ = YK) (kP : P₁ * YK = YK)
    (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁)
    (sP : P₁ * Y₁ = Y₁) (sQ : Y₁ * Q₁ = Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) :
    ∃ Ξ : Matrix m m ℝ, P₁ * Ξ = Ξ ∧ Ξ - h • (P₁ * (M * Ξ)) = P₁ * (1 - h • (P₀ * M)) ∧
      √(‖Y₁ - Yt‖ ^ 2 + h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2) ≤
        (2 + h * μ) * ‖h • ((Ξ - P₁) * YL * (Cᵀ * C))‖ +
          ‖h • (M * (YK - Y₁) - P₁ * (M * (YK - Y₁)))‖ := by
  obtain ⟨Ξ, D, hΞP, hΞ, hDe, hmain⟩ := exists_sq_norm_sub_backwardEuler_add_le hP₁ hP₁t hQ₀
    hQ₀t hQ₁t kEq kQ kP lEq lP lQ sEq sP sQ hdiss hμ0 hμ hh hYt
  refine ⟨Ξ, hΞP, hΞ, ?_⟩
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  have s1 : ∀ A : Matrix m n ℝ, h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), A⟫ ≤
      ‖h • ((Ξ - P₁) * YL * (Cᵀ * C))‖ * ‖A‖ := fun A => by
    rw [← real_inner_smul_left]; exact real_inner_le_norm _ _
  have s2 : h * ⟪M * (YK - Y₁) - P₁ * (M * (YK - Y₁)), Y₁ - Yt⟫ ≤
      ‖h • (M * (YK - Y₁) - P₁ * (M * (YK - Y₁)))‖ * ‖Y₁ - Yt‖ := by
    rw [← real_inner_smul_left]; exact real_inner_le_norm _ _
  have hD : ‖D‖ ^ 2 + (√h * ‖D * Cᵀ‖) ^ 2 ≤ ‖h • ((Ξ - P₁) * YL * (Cᵀ * C))‖ * ‖D‖ := by
    have := s1 (-D)
    rw [inner_neg_right, norm_neg, mul_neg] at this
    rw [mul_pow, hs2]
    exact hDe.trans this
  have hfin := local_scalar' (η := h * μ)
    (r := ‖h • (M * (YK - Y₁) - P₁ * (M * (YK - Y₁)))‖) (norm_nonneg (Y₁ - Yt))
    (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg ((Y₁ - Yt) * Cᵀ))) (norm_nonneg D)
    (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg (D * Cᵀ))) (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg hh.le hμ0) hD (by rw [mul_pow, hs2]; linarith [s1 (Y₁ - Yt)])
  rw [mul_pow, hs2] at hfin
  exact hfin

/-- **The local error bound**, in terms of the projectors. For a step of the BUG integrator with
backward Euler substeps and the backward Euler step `Ỹ` of the full problem from the same start
value, for every matrix `Z` and without a restriction on `h μ`,

  `√(‖Y₁ - Ỹ‖² + 2 h ‖(Y₁ - Ỹ) Cᵀ‖²) ≤`
  `    (27/4 + 2 h μ) h μ min(‖Y₀‖, √h ‖(Y₀ - Z) Cᵀ‖ / 2 + h ‖Z CᵀC‖)`. -/
theorem sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors
    (hP₀ : P₀ * P₀ = P₀) (hP₀t : P₀ᵀ = P₀) (hP₁ : P₁ * P₁ = P₁) (hP₁t : P₁ᵀ = P₁)
    (hQ₀ : Q₀ * Q₀ = Q₀) (hQ₀t : Q₀ᵀ = Q₀) (hQ₁t : Q₁ᵀ = Q₁)
    (kEq : YK = Y₀ + h • ((M * YK - YK * (Cᵀ * C)) * Q₀))
    (kQ : YK * Q₀ = YK) (kP : P₁ * YK = YK) (yQ : Y₀ * Q₀ = Y₀)
    (lEq : YL = Y₀ + h • (P₀ * (M * YL - YL * (Cᵀ * C))))
    (lP : P₀ * YL = YL) (lQ : YL * Q₁ = YL)
    (sEq : Y₁ = P₁ * (Y₀ + h • (M * Y₁ - Y₁ * (Cᵀ * C))) * Q₁)
    (sP : P₁ * Y₁ = Y₁) (sQ : Y₁ * Q₁ = Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0)
    (hμ0 : 0 ≤ μ) (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = Y₀) (Z : Matrix m n ℝ) :
    √(‖Y₁ - Yt‖ ^ 2 + 2 * (h * ‖(Y₁ - Yt) * Cᵀ‖ ^ 2)) ≤
      (27 / 4 + 2 * (h * μ)) * (h * μ) *
        min ‖Y₀‖ (√h * ‖(Y₀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) := by
  classical
  obtain ⟨Ξ, D, hΞP, hΞ, hDe, hmain⟩ := exists_sq_norm_sub_backwardEuler_add_le hP₁ hP₁t hQ₀
    hQ₀t hQ₁t kEq kQ kP lEq lP lQ sEq sP sQ hdiss hμ0 hμ hh hYt
  obtain ⟨Λ, eqK, -, hΛ1, hΛ2⟩ := exists_kstep_gram_term hQ₀ hQ₀t kEq kQ kP hdiss hh
  obtain ⟨η, hη⟩ : ∃ η, η = h * μ := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; exact mul_nonneg hh.le hμ0
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = min ‖Y₀‖ (√h * ‖(Y₀ - Z) * Cᵀ‖ / 2 +
      h * ‖Z * (Cᵀ * C)‖) := ⟨_, rfl⟩
  rw [← hη, ← hlam]
  rw [← hη] at hmain
  have hs2 : √h ^ 2 = h := Real.sq_sqrt hh.le
  -- the three stiff terms are bounded by `lam`
  have b1 : ‖Λ‖ ≤ lam := by rw [hlam]; exact le_min hΛ1 (hΛ2 Z)
  have b2 : ‖h • (YL * (Cᵀ * C))‖ ≤ lam := by
    obtain ⟨g1, g2⟩ := norm_smul_mul_gram_le (C := C) hdiss hP₀t hh lP
      (start_eq_of_lstep lEq lP).symm
    rw [hlam]; exact le_min g1 (g2 Z)
  have b3 : ‖h • (Yt * (Cᵀ * C))‖ ≤ lam := by
    obtain ⟨g1, g2⟩ := norm_smul_backwardEuler_mul_gram_le hdiss hh hYt
    rw [hlam]; exact le_min g1 (g2 Z)
  have hlam0 : 0 ≤ lam := (norm_nonneg Λ).trans b1
  -- the K-step against the backward Euler step
  have hκ : ‖YK - Yt‖ ≤ 9 / 4 * lam := by
    have := sq_norm_kstep_sub_backwardEuler_le hQ₀ hQ₀t yQ kQ hdiss hh eqK hYt
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [norm_nonneg Λ, norm_nonneg (h • (Yt * (Cᵀ * C))), norm_nonneg (YK - Yt),
      mul_le_mul b1 b1 (norm_nonneg Λ) hlam0, mul_le_mul b3 b3 (norm_nonneg _) hlam0,
      mul_le_mul b1 b3 (norm_nonneg _) hlam0]
  -- the stiff source
  have s0 : ‖h • ((Ξ - P₁) * YL * (Cᵀ * C))‖ ≤ 2 * η * lam := by
    have e : h • ((Ξ - P₁) * YL * (Cᵀ * C)) = (Ξ - P₁) * (h • (YL * (Cᵀ * C))) := by
      rw [Matrix.mul_smul, Matrix.mul_assoc]
    have := norm_xi_sub_mul_le hdiss hμ0 hμ hh.le hP₀ hP₀t hP₁ hP₁t hΞP hΞ
      (h • (YL * (Cᵀ * C)))
    rw [e, hη]
    exact this.trans (mul_le_mul_of_nonneg_left b2
      (mul_nonneg zero_le_two (mul_nonneg hh.le hμ0)))
  have s1 : ∀ A : Matrix m n ℝ, h * ⟪(Ξ - P₁) * YL * (Cᵀ * C), A⟫ ≤ 2 * η * lam * ‖A‖ :=
    fun A => by
      rw [← real_inner_smul_left]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right s0 (norm_nonneg A))
  have hD : ‖D‖ ^ 2 + (√h * ‖D * Cᵀ‖) ^ 2 ≤ 2 * η * lam * ‖D‖ := by
    have := s1 (-D)
    rw [inner_neg_right, norm_neg, mul_neg] at this
    rw [mul_pow, hs2]
    exact hDe.trans this
  -- the normal part of the K-step
  have s2 : h * ⟪M * (YK - Y₁) - P₁ * (M * (YK - Y₁)), Y₁ - Yt⟫ ≤
      η * (9 / 4 * lam) * ‖Y₁ - Yt‖ := by
    have n1 := inner_sub_proj_mul_le (Yt := Yt) hP₁ hP₁t hμ0 hμ kP sP
    have n2 := mul_le_mul_of_nonneg_left n1 hh.le
    have n3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ hη0)
      (norm_nonneg (Y₁ - Yt))
    have e : h * (μ * ‖YK - Yt‖ * ‖Y₁ - Yt‖) = η * ‖YK - Yt‖ * ‖Y₁ - Yt‖ := by rw [hη]; ring
    linarith
  have hfin := local_scalar (x := ‖Y₁ - Yt‖) (E := √h * ‖(Y₁ - Yt) * Cᵀ‖) (κ := 9 / 4 * lam)
    (η := η) (norm_nonneg D)
    (mul_nonneg (Real.sqrt_nonneg h) (norm_nonneg (D * Cᵀ)))
    (mul_nonneg (mul_nonneg zero_le_two hη0) hlam0) (by positivity) hη0 hD
    (by rw [mul_pow, hs2]; linarith [s1 (Y₁ - Yt)])
  rw [mul_pow, hs2] at hfin
  refine hfin.trans (le_of_eq ?_)
  ring

end Lemmas

end ImplicitBUGStiffLocal

open ImplicitBUGStiffLocal

section Step

variable {m n k k₁ k₂ : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k₁] [Fintype k₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {M : Matrix m m ℝ} {C : Matrix k n ℝ} {ε ϑ t₁ h μ : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ Yt : Matrix m n ℝ}

/-- The projector relations of a step of the matrix integrator with exact capture for
`F(Z) = M Z - Z CᵀC`: the projectors `P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ`, `Q₀ = V₀ V₀ᵀ`, `Q₁ = V₁ V₁ᵀ`
are orthogonal projectors, and `Y_K = K₁ V₀ᵀ`, `Y_L = U₀ L₁ᵀ`, `Ŷ₁ = U₁ S₁ V₁ᵀ` solve the K-, L- and
S-step equations in projector form. -/
theorem IsMatrixImplicitBUGStep.projector_relations_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) :
    ((U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ ∧ (U₀ * U₀ᵀ)ᵀ = U₀ * U₀ᵀ) ∧
      (U₁ * U₁ᵀ * (U₁ * U₁ᵀ) = U₁ * U₁ᵀ ∧ (U₁ * U₁ᵀ)ᵀ = U₁ * U₁ᵀ) ∧
      (V₀ * V₀ᵀ * (V₀ * V₀ᵀ) = V₀ * V₀ᵀ ∧ (V₀ * V₀ᵀ)ᵀ = V₀ * V₀ᵀ) ∧
      (V₁ * V₁ᵀ)ᵀ = V₁ * V₁ᵀ) ∧
    (K₁ * V₀ᵀ = U₀ * S₀ * V₀ᵀ +
        h • ((M * (K₁ * V₀ᵀ) - K₁ * V₀ᵀ * (Cᵀ * C)) * (V₀ * V₀ᵀ)) ∧
      K₁ * V₀ᵀ * (V₀ * V₀ᵀ) = K₁ * V₀ᵀ ∧ U₁ * U₁ᵀ * (K₁ * V₀ᵀ) = K₁ * V₀ᵀ ∧
      U₀ * S₀ * V₀ᵀ * (V₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ ∧
      U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ) ∧
    (U₀ * L₁ᵀ = U₀ * S₀ * V₀ᵀ +
        h • (U₀ * U₀ᵀ * (M * (U₀ * L₁ᵀ) - U₀ * L₁ᵀ * (Cᵀ * C))) ∧
      U₀ * U₀ᵀ * (U₀ * L₁ᵀ) = U₀ * L₁ᵀ ∧ U₀ * L₁ᵀ * (V₁ * V₁ᵀ) = U₀ * L₁ᵀ) ∧
    (U₁ * S₁ * V₁ᵀ = U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ +
        h • (M * (U₁ * S₁ * V₁ᵀ) - U₁ * S₁ * V₁ᵀ * (Cᵀ * C))) * (V₁ * V₁ᵀ) ∧
      U₁ * U₁ᵀ * (U₁ * S₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ ∧
      U₁ * S₁ * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ) := by
  have hP₀ : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have hP₁ : U₁ * U₁ᵀ * (U₁ * U₁ᵀ) = U₁ * U₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have hQ₀ : V₀ * V₀ᵀ * (V₀ * V₀ᵀ) = V₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have hP₀t : (U₀ * U₀ᵀ)ᵀ = U₀ * U₀ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP₁t : (U₁ * U₁ᵀ)ᵀ = U₁ * U₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ₀t : (V₀ * V₀ᵀ)ᵀ = V₀ * V₀ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQ₁t : (V₁ * V₁ᵀ)ᵀ = V₁ * V₁ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have kEq : K₁ * V₀ᵀ = U₀ * S₀ * V₀ᵀ +
      h • ((M * (K₁ * V₀ᵀ) - K₁ * V₀ᵀ * (Cᵀ * C)) * (V₀ * V₀ᵀ)) := by
    have := congrArg (fun A => A * V₀ᵀ) hs.kstep
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have kQ : K₁ * V₀ᵀ * (V₀ * V₀ᵀ) = K₁ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have kP : U₁ * U₁ᵀ * (K₁ * V₀ᵀ) = K₁ * V₀ᵀ := by
    have := norm_le_zero_iff.1 hs.kcap
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm
  have yQ : U₀ * S₀ * V₀ᵀ * (V₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₀]
  have yP : U₀ * U₀ᵀ * (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have lEq : U₀ * L₁ᵀ = U₀ * S₀ * V₀ᵀ +
      h • (U₀ * U₀ᵀ * (M * (U₀ * L₁ᵀ) - U₀ * L₁ᵀ * (Cᵀ * C))) := by
    have := congrArg (fun A => U₀ * Aᵀ) hs.lstep
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have lP : U₀ * U₀ᵀ * (U₀ * L₁ᵀ) = U₀ * L₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₀]
  have lQ : U₀ * L₁ᵀ * (V₁ * V₁ᵀ) = U₀ * L₁ᵀ := by
    have := norm_le_zero_iff.1 hs.lcap
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have sEq : U₁ * S₁ * V₁ᵀ = U₁ * U₁ᵀ * (U₀ * S₀ * V₀ᵀ +
      h • (M * (U₁ * S₁ * V₁ᵀ) - U₁ * S₁ * V₁ᵀ * (Cᵀ * C))) * (V₁ * V₁ᵀ) := by
    have := congrArg (fun A => U₁ * A * V₁ᵀ) hs.sstep
    simp only [Matrix.mul_assoc] at this
    simpa only [Matrix.mul_assoc] using this
  have sP : U₁ * U₁ᵀ * (U₁ * S₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthU₁]
  have sQ : U₁ * S₁ * V₁ᵀ * (V₁ * V₁ᵀ) = U₁ * S₁ * V₁ᵀ := by
    simp only [Matrix.mul_assoc, orth_mul_cancel hs.orthV₁]
  exact ⟨⟨⟨hP₀, hP₀t⟩, ⟨hP₁, hP₁t⟩, ⟨hQ₀, hQ₀t⟩, hQ₁t⟩, ⟨kEq, kQ, kP, yQ, yP⟩, ⟨lEq, lP, lQ⟩,
    sEq, sP, sQ⟩

/-- **The local error bound for a step of the matrix integrator.** Let `F(Z) = M Z - Z CᵀC` with
`M` dissipative and bounded by `μ`, and let `Ỹ - h M Ỹ + h Ỹ CᵀC = U₀ S₀ V₀ᵀ` (the backward Euler
step of the full problem from the start value of the step). For a step with exact capture, new
bases of any size (fixed rank or augmented), any normal defect and any truncation tolerance, the
result `Ŷ₁ = U₁ S₁ V₁ᵀ` of the Galerkin step before truncation satisfies, for every matrix `Z`,

  `√(‖Ŷ₁ - Ỹ‖² + 2 h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤`
  `    (27/4 + 2 h μ) h μ min(‖Y₀‖, √h ‖(Y₀ - Z) Cᵀ‖ / 2 + h ‖Z CᵀC‖)`,   `Y₀ = U₀ S₀ V₀ᵀ`.

There is no restriction on `h μ`; the matrix `C` enters only through the stiff energy of
`Y₀ - Z` and through `‖Z CᵀC‖`, and the singular values of `S₀` do not enter. -/
theorem IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ) (Z : Matrix m n ℝ) :
    √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + 2 * (h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * Cᵀ‖ ^ 2)) ≤
      (27 / 4 + 2 * (h * μ)) * (h * μ) * min ‖U₀ * S₀ * V₀ᵀ‖
        (√h * ‖(U₀ * S₀ * V₀ᵀ - Z) * Cᵀ‖ / 2 + h * ‖Z * (Cᵀ * C)‖) := by
  obtain ⟨⟨⟨hP₀, hP₀t⟩, ⟨hP₁, hP₁t⟩, ⟨hQ₀, hQ₀t⟩, hQ₁t⟩, ⟨kEq, kQ, kP, yQ, -⟩, ⟨lEq, lP, lQ⟩,
    sEq, sP, sQ⟩ := hs.projector_relations_of_sylvester
  exact sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors hP₀ hP₀t hP₁ hP₁t hQ₀ hQ₀t hQ₁t kEq
    kQ kP yQ lEq lP lQ sEq sP sQ hdiss hμ0 hμ hh hYt Z

/-- **The local error of a step of the matrix integrator in terms of quantities of the step.**
In the setting of
`IsMatrixImplicitBUGStep.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester`, with
`P₀ = U₀ U₀ᵀ`, `P₁ = U₁ U₁ᵀ` and the Galerkin resolvent `Ξ` of the new column space
(`P₁ Ξ = Ξ`, `Ξ - h P₁ M Ξ = P₁ (1 - h P₀ M)`),

  `√(‖Ŷ₁ - Ỹ‖² + h ‖(Ŷ₁ - Ỹ) Cᵀ‖²) ≤`
  `    (2 + h μ) ‖h (Ξ - P₁) U₀ L₁ᵀ CᵀC‖ + ‖h (1 - P₁) M (K₁ V₀ᵀ - Ŷ₁)‖`.

The right-hand side does not contain the backward Euler step `Ỹ`. -/
theorem IsMatrixImplicitBUGStep.exists_sqrt_sq_norm_galerkin_sub_backwardEuler_add_le
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) => M * Z - Z * (Cᵀ * C)) ε 0 ϑ
      t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hdiss : ∀ x : m → ℝ, x ⬝ᵥ M *ᵥ x ≤ 0) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : m → ℝ, M *ᵥ x ⬝ᵥ M *ᵥ x ≤ μ ^ 2 * (x ⬝ᵥ x)) (hh : 0 < h)
    (hYt : Yt - h • (M * Yt) + h • (Yt * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ) :
    ∃ Ξ : Matrix m m ℝ, U₁ * U₁ᵀ * Ξ = Ξ ∧
      Ξ - h • (U₁ * U₁ᵀ * (M * Ξ)) = U₁ * U₁ᵀ * (1 - h • (U₀ * U₀ᵀ * M)) ∧
      √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * Cᵀ‖ ^ 2) ≤
        (2 + h * μ) * ‖h • ((Ξ - U₁ * U₁ᵀ) * (U₀ * L₁ᵀ) * (Cᵀ * C))‖ +
          ‖h • (M * (K₁ * V₀ᵀ - U₁ * S₁ * V₁ᵀ) -
            U₁ * U₁ᵀ * (M * (K₁ * V₀ᵀ - U₁ * S₁ * V₁ᵀ)))‖ := by
  obtain ⟨⟨-, ⟨hP₁, hP₁t⟩, ⟨hQ₀, hQ₀t⟩, hQ₁t⟩, ⟨kEq, kQ, kP, -, -⟩, ⟨lEq, lP, lQ⟩,
    sEq, sP, sQ⟩ := hs.projector_relations_of_sylvester
  exact exists_sqrt_sq_norm_sub_backwardEuler_add_le_of_projectors hP₁ hP₁t hQ₀ hQ₀t hQ₁t kEq
    kQ kP lEq lP lQ sEq sP sQ hdiss hμ0 hμ hh hYt

end Step

/-! ### Non-vacuity -/

namespace ImplicitBUGStiffLocalExample

open ImplicitBUGStiffLemmasExample

local notation "Mₗ" => (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)

local notation "Cₗ" lam => (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)

local notation "Bₗ" => (!![9 / 25, 12 / 25; 12 / 25, 16 / 25] : Matrix (Fin 2) (Fin 2) ℝ)

/-- A step from `(3/5, 4/5)ᵀ (3/5, 4/5)` exists for the family `M = diag(0, -1)`,
`C = (0, √lam)`: the rows of the start value are not in the kernel of `CᵀC`. -/
theorem exists_isMatrixImplicitBUGStep {h lam : ℝ} (hh : 0 < h) (hlam : 0 ≤ lam) :
    ∃ (K₁ L₁ U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (Y₁ : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ),
      IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
        Mₗ * Z - Z * ((Cₗ lam)ᵀ * (Cₗ lam))) ε 0 0 0 h !![3 / 5; 4 / 5] 1 !![3 / 5; 4 / 5] K₁ L₁
        U₁ V₁ S₁ Y₁ := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := StiffRowsExample.exists_isMatrixImplicitBUGStep
    (c := 3 / 5) (s := 4 / 5) hh.le hlam (by norm_num) 0
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -1] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      Mₗ * Z - Z * ((Cₗ lam)ᵀ * (Cₗ lam)) := by
    funext _ Z
    rw [transpose_mul_self_eq lam hlam, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  exact ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩

/-- The start value `(3/5, 4/5)ᵀ (3/5, 4/5)` as a matrix. -/
theorem start_eq : (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ) *
    (1 : Matrix (Fin 1) (Fin 1) ℝ) * (!![3 / 5; 4 / 5] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ = Bₗ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> norm_num

/-- The rows of the start value are not in the kernel of `CᵀC` for `lam > 0`. -/
theorem start_mul_gram_ne_zero {lam : ℝ} (hlam : 0 < lam) :
    Bₗ * ((Cₗ lam)ᵀ * (Cₗ lam)) ≠ 0 := by
  rw [transpose_mul_self_eq lam hlam.le]
  intro h0
  have e : (Bₗ * -!![0, 0; 0, -lam]) 0 1 = 12 / 25 * lam := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h0, Matrix.zero_apply] at e
  have : 0 < 12 / 25 * lam := by positivity
  linarith

/-- The hypotheses of the local error bound hold for this family, for every stiffness `lam > 0`
and every `h > 0`: a step from a start value whose rows are not in the kernel of `CᵀC`, and the
backward Euler step of the full problem from the same start value. -/
example {h lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) :
    Bₗ * ((Cₗ lam)ᵀ * (Cₗ lam)) ≠ 0 ∧
    ∃ (U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (Yt : Matrix (Fin 2) (Fin 2) ℝ),
      Yt - h • (Mₗ * Yt) + h • (Yt * ((Cₗ lam)ᵀ * (Cₗ lam))) = Bₗ ∧
      ∀ Z : Matrix (Fin 2) (Fin 2) ℝ,
        √(‖U₁ * S₁ * V₁ᵀ - Yt‖ ^ 2 + 2 * (h * ‖(U₁ * S₁ * V₁ᵀ - Yt) * (Cₗ lam)ᵀ‖ ^ 2)) ≤
          (27 / 4 + 2 * (h * 1)) * (h * 1) * min ‖Bₗ‖
            (√h * ‖(Bₗ - Z) * (Cₗ lam)ᵀ‖ / 2 + h * ‖Z * ((Cₗ lam)ᵀ * (Cₗ lam))‖) := by
  refine ⟨start_mul_gram_ne_zero hlam, ?_⟩
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ := exists_isMatrixImplicitBUGStep hh hlam.le
  obtain ⟨Yt, hYt⟩ := exists_backwardEuler (C := Cₗ lam) dotProduct_mulVec_nonpos hh.le Bₗ
  refine ⟨U₁, V₁, S₁, Yt, hYt, fun Z => ?_⟩
  have := hs.sqrt_sq_norm_galerkin_sub_backwardEuler_add_le_of_sylvester dotProduct_mulVec_nonpos
    zero_le_one dotProduct_mulVec_mulVec_le hh (by rw [start_eq]; exact hYt) Z
  rwa [start_eq] at this

end ImplicitBUGStiffLocalExample

end LeanDLRA

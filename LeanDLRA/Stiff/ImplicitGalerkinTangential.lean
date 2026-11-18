import LeanDLRA.Stiff.ImplicitBUG

/-!
# Implicit Galerkin steps for fields with a stiff linear part: where the stiff part enters

Let `F(t, ·) = S + G` with `S` additive (the stiff part, for matrices `S(Z) = M Z + Z N`) and `G`
Lipschitz with the constant `L`. Every substep of the BUG integrator with backward Euler substeps
is an implicit Galerkin step `x₁ = P (x₀ + h F(t, x₁))` with an orthogonal projector `P`
(`P = Q₀` in the K-step, `P = P₀` in the L-step, `P = P₁ Q₁` in the S-step). This file compares
such a step with an arbitrary pair of reference states `u₀`, `u₁` (a reference curve at the two
ends of the step):

  `(1 - h ℓ) ‖x₁ - P u₁‖ ≤ ‖x₀ - u₀‖ + ‖P (u₁ - u₀ - h F(t, u₁))‖ + h ‖P S (u₁ - P u₁)‖`
  `    + h L ‖u₁ - P u₁‖`.

The stiff part enters through the one-sided Lipschitz constant `ℓ` of `F`, through the backward
Euler defect of the reference, and through `P S (1 - P) u₁`: the block of `S` that maps the
complement of the Galerkin space into it, applied to the part of the reference that the Galerkin
space does not contain. This block vanishes if `S` commutes with `P`. For `S(Z) = M Z + Z N` the
K-step sees `u₁ (1 - Q₀) N Q₀` and the L-step `P₀ M (1 - P₀) u₁`, with the projectors of the
numerical solution.

## Main results

* `implicitGalerkin_compare_residual_le_of_add`: the residual of the projected reference.
* `implicitGalerkin_compare_of_add`: the comparison above.
* `apply_apply_sub_apply_eq_zero_of_comm`: `P S (u - P u) = 0` if `S` commutes with `P`.
* `IsImplicitBUGStep.norm_kstep_sub_le_of_add`, `IsImplicitBUGStep.norm_lstep_sub_le_of_add`,
  `IsImplicitBUGStep.norm_sstep_sub_le_of_add`: the three substeps of
  `IsImplicitBUGStep`.
* `sylvester_sub_mul_mul_eq`, `mul_sylvester_sub_mul_eq`: the block for the Sylvester operator
  and a right, respectively left, projector.
* `IsMatrixImplicitBUGStep.norm_kstep_sub_le_of_sylvester_add`,
  `IsMatrixImplicitBUGStep.norm_lstep_sub_le_of_sylvester_add`: the K- and the L-step of the
  matrix integrator for `F(t, Z) = M Z + Z N + G(t, Z)`.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
* [KieriVandereycken2019] for the one-sided Lipschitz setting.
-/

open scoped RealInnerProductSpace

namespace LeanDLRA

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
  {S G : E → E} {P : E →L[ℝ] E} {h ℓ L t : ℝ}

/-- **The residual of the projected reference for a field with an additive part.** Let
`F(t, ·) = S + G` with `S` additive and `‖G u₁ - G (P u₁)‖ ≤ L ‖u₁ - P u₁‖`. Then the residual of
`P u₁` in the implicit Galerkin step from `u₀` satisfies

  `‖P u₁ - P (u₀ + h F(t, P u₁))‖ ≤ ‖P (u₁ - u₀ - h F(t, u₁))‖ + h ‖P S (u₁ - P u₁)‖`
  `    + h L ‖u₁ - P u₁‖`.

No bound of `S` occurs: only its block from the complement of the range of `P` into the range,
applied to `u₁ - P u₁`. -/
theorem implicitGalerkin_compare_residual_le_of_add (hP : IsOrthProj P) (hh : 0 ≤ h)
    {u₀ u₁ : E} (hF : ∀ z, F t z = S z + G z) (hS : ∀ z w, S (z - w) = S z - S w)
    (hG : ‖G u₁ - G (P u₁)‖ ≤ L * ‖u₁ - P u₁‖) :
    ‖P u₁ - P (u₀ + h • F t (P u₁))‖ ≤
      ‖P (u₁ - u₀ - h • F t u₁)‖ + h * ‖P (S (u₁ - P u₁))‖ + h * L * ‖u₁ - P u₁‖ := by
  have e : P u₁ - P (u₀ + h • F t (P u₁)) =
      P (u₁ - u₀ - h • F t u₁) + h • P (S (u₁ - P u₁)) + h • P (G u₁ - G (P u₁)) := by
    rw [hS, hF u₁, hF (P u₁)]
    simp only [map_sub, map_add, map_smul, smul_add, smul_sub]
    abel
  have h3 := mul_le_mul_of_nonneg_left ((hP.norm_le (G u₁ - G (P u₁))).trans hG) hh
  rw [e]
  refine (norm_add₃_le).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hh]
  linarith [mul_assoc h L ‖u₁ - P u₁‖]

/-- **An implicit Galerkin step against a reference, for a field with an additive part.** Let
`x₁ = P (x₀ + h F(t, x₁))`, `F(t, ·) = S + G` with `S` additive,
`‖G u₁ - G (P u₁)‖ ≤ L ‖u₁ - P u₁‖`, and let `F(t, ·)` satisfy the one-sided inequality with the
constant `ℓ` at the pair `(x₁, P u₁)`. Then for all `u₀`

  `(1 - h ℓ) ‖x₁ - P u₁‖ ≤ ‖x₀ - u₀‖ + ‖P (u₁ - u₀ - h F(t, u₁))‖ + h ‖P S (u₁ - P u₁)‖`
  `    + h L ‖u₁ - P u₁‖`. -/
theorem implicitGalerkin_compare_of_add (hP : IsOrthProj P) (hh : 0 ≤ h) {x₀ x₁ u₀ u₁ : E}
    (hx : x₁ = P (x₀ + h • F t x₁)) (hF : ∀ z, F t z = S z + G z)
    (hS : ∀ z w, S (z - w) = S z - S w) (hG : ‖G u₁ - G (P u₁)‖ ≤ L * ‖u₁ - P u₁‖)
    (hos : ⟪F t x₁ - F t (P u₁), x₁ - P u₁⟫ ≤ ℓ * ‖x₁ - P u₁‖ ^ 2) :
    (1 - h * ℓ) * ‖x₁ - P u₁‖ ≤
      ‖x₀ - u₀‖ + ‖P (u₁ - u₀ - h • F t u₁)‖ + h * ‖P (S (u₁ - P u₁))‖ +
        h * L * ‖u₁ - P u₁‖ := by
  have h1 := implicitGalerkin_compare hP hh (u₀ := u₀) hx hos
  have h2 := implicitGalerkin_compare_residual_le_of_add hP hh (u₀ := u₀) hF hS hG
  linarith

/-- **No stiff block for a commuting projector.** If the additive map `S` commutes with the
projector `P`, then `P S (u - P u) = 0`. -/
theorem apply_apply_sub_apply_eq_zero_of_comm (hP : IsOrthProj P)
    (hS : ∀ z w, S (z - w) = S z - S w) (hc : ∀ z, P (S z) = S (P z)) (u : E) :
    P (S (u - P u)) = 0 := by
  rw [hc, map_sub, hP.idem, hS, sub_self]

end Abstract

namespace IsImplicitBUGStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : ℝ → E → E}
  {S G : E → E} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {ε τ ϑ t₁ h ℓ L : ℝ} {Y₀ YK YL xS Y₁ : E}

/-- **The K-step against a reference.** In an implicit BUG step from `Y₀ = Q₀ Y₀` for a field
`F(t₁, ·) = S + G` with `S` additive, the K-step result satisfies for all reference states
`X₀`, `X₁`

  `(1 - h ℓ) ‖YK - Q₀ X₁‖ ≤ ‖Y₀ - X₀‖ + ‖Q₀ (X₁ - X₀ - h F(t₁, X₁))‖ + h ‖Q₀ S (X₁ - Q₀ X₁)‖`
  `    + h L ‖X₁ - Q₀ X₁‖`. -/
theorem norm_kstep_sub_le_of_add (hs : IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁)
    (hh : 0 ≤ h) (hY₀ : Q₀ Y₀ = Y₀) {X₀ X₁ : E} (hF : ∀ z, F t₁ z = S z + G z)
    (hS : ∀ z w, S (z - w) = S z - S w) (hG : ‖G X₁ - G (Q₀ X₁)‖ ≤ L * ‖X₁ - Q₀ X₁‖)
    (hos : ⟪F t₁ YK - F t₁ (Q₀ X₁), YK - Q₀ X₁⟫ ≤ ℓ * ‖YK - Q₀ X₁‖ ^ 2) :
    (1 - h * ℓ) * ‖YK - Q₀ X₁‖ ≤
      ‖Y₀ - X₀‖ + ‖Q₀ (X₁ - X₀ - h • F t₁ X₁)‖ + h * ‖Q₀ (S (X₁ - Q₀ X₁))‖ +
        h * L * ‖X₁ - Q₀ X₁‖ :=
  implicitGalerkin_compare_of_add hs.hQ₀ hh
    (by rw [map_add, map_smul, hY₀]; exact hs.kstep) hF hS hG hos

/-- **The L-step against a reference.** In an implicit BUG step from `Y₀ = P₀ Y₀` for a field
`F(t₁, ·) = S + G` with `S` additive, the L-step result satisfies for all reference states
`X₀`, `X₁`

  `(1 - h ℓ) ‖YL - P₀ X₁‖ ≤ ‖Y₀ - X₀‖ + ‖P₀ (X₁ - X₀ - h F(t₁, X₁))‖ + h ‖P₀ S (X₁ - P₀ X₁)‖`
  `    + h L ‖X₁ - P₀ X₁‖`. -/
theorem norm_lstep_sub_le_of_add (hs : IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁)
    (hh : 0 ≤ h) (hY₀ : P₀ Y₀ = Y₀) {X₀ X₁ : E} (hF : ∀ z, F t₁ z = S z + G z)
    (hS : ∀ z w, S (z - w) = S z - S w) (hG : ‖G X₁ - G (P₀ X₁)‖ ≤ L * ‖X₁ - P₀ X₁‖)
    (hos : ⟪F t₁ YL - F t₁ (P₀ X₁), YL - P₀ X₁⟫ ≤ ℓ * ‖YL - P₀ X₁‖ ^ 2) :
    (1 - h * ℓ) * ‖YL - P₀ X₁‖ ≤
      ‖Y₀ - X₀‖ + ‖P₀ (X₁ - X₀ - h • F t₁ X₁)‖ + h * ‖P₀ (S (X₁ - P₀ X₁))‖ +
        h * L * ‖X₁ - P₀ X₁‖ :=
  implicitGalerkin_compare_of_add hs.hP₀ hh
    (by rw [map_add, map_smul, hY₀]; exact hs.lstep) hF hS hG hos

/-- **The S-step against a reference.** In an implicit BUG step for a field
`F(t₁, ·) = S + G` with `S` additive, the result of the Galerkin step satisfies, with
`R = P₁ Q₁` and for all reference states `X₀`, `X₁`,

  `(1 - h ℓ) ‖xS - R X₁‖ ≤ ‖Y₀ - X₀‖ + ‖R (X₁ - X₀ - h F(t₁, X₁))‖ + h ‖R S (X₁ - R X₁)‖`
  `    + h L ‖X₁ - R X₁‖`. -/
theorem norm_sstep_sub_le_of_add (hs : IsImplicitBUGStep F ε τ ϑ P₀ Q₀ P₁ Q₁ t₁ h Y₀ YK YL xS Y₁)
    (hh : 0 ≤ h) {X₀ X₁ : E} (hF : ∀ z, F t₁ z = S z + G z)
    (hS : ∀ z w, S (z - w) = S z - S w)
    (hG : ‖G X₁ - G ((P₁ * Q₁) X₁)‖ ≤ L * ‖X₁ - (P₁ * Q₁) X₁‖)
    (hos : ⟪F t₁ xS - F t₁ ((P₁ * Q₁) X₁), xS - (P₁ * Q₁) X₁⟫ ≤
      ℓ * ‖xS - (P₁ * Q₁) X₁‖ ^ 2) :
    (1 - h * ℓ) * ‖xS - (P₁ * Q₁) X₁‖ ≤
      ‖Y₀ - X₀‖ + ‖(P₁ * Q₁) (X₁ - X₀ - h • F t₁ X₁)‖ +
        h * ‖(P₁ * Q₁) (S (X₁ - (P₁ * Q₁) X₁))‖ + h * L * ‖X₁ - (P₁ * Q₁) X₁‖ :=
  implicitGalerkin_compare_of_add hs.proj hh hs.sstep hF hS hG hos

end IsImplicitBUGStep

section Sylvester

variable {m n : Type*} [Fintype m] [Fintype n]

/-- **The stiff block of the K-step for the Sylvester operator.** For an idempotent `Q`,
`(M (X - X Q) + (X - X Q) N) Q = X (1 - Q) N Q`: the left factor `M` does not enter, and the right
factor enters through its block between the range of `Q` and its complement. -/
theorem sylvester_sub_mul_mul_eq [DecidableEq n] {Q : Matrix n n ℝ} (hQ : Q * Q = Q)
    (M : Matrix m m ℝ) (N : Matrix n n ℝ) (X : Matrix m n ℝ) :
    (M * (X - X * Q) + (X - X * Q) * N) * Q = X * (1 - Q) * N * Q := by
  have h1 : M * (X - X * Q) * Q = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc X Q Q, hQ, sub_self, Matrix.mul_zero]
  rw [Matrix.add_mul, h1, zero_add, Matrix.mul_sub, Matrix.mul_one]

/-- **The stiff block of the L-step for the Sylvester operator.** For an idempotent `P`,
`P (M (X - P X) + (X - P X) N) = P M (1 - P) X`. -/
theorem mul_sylvester_sub_mul_eq [DecidableEq m] {P : Matrix m m ℝ} (hP : P * P = P)
    (M : Matrix m m ℝ) (N : Matrix n n ℝ) (X : Matrix m n ℝ) :
    P * (M * (X - P * X) + (X - P * X) * N) = P * M * (1 - P) * X := by
  have h1 : P * ((X - P * X) * N) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc P P X, hP, sub_self,
      Matrix.zero_mul]
  rw [Matrix.mul_add, h1, add_zero, Matrix.mul_assoc P M, Matrix.mul_assoc P,
    Matrix.mul_assoc M, Matrix.sub_mul, Matrix.one_mul]

end Sylvester

namespace IsMatrixImplicitBUGStep

open scoped Matrix LeanDLRA.Frobenius

variable {m n k k' : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype k'] [DecidableEq m]
  [DecidableEq n] [DecidableEq k] [DecidableEq k'] {r : ℕ} {M : Matrix m m ℝ} {N : Matrix n n ℝ}
  {G : ℝ → Matrix m n ℝ → Matrix m n ℝ} {ε τ ϑ t₁ h ℓ L : ℝ} {U₀ : Matrix m (Fin r) ℝ}
  {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ} {K₁ : Matrix m (Fin r) ℝ}
  {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k ℝ} {V₁ : Matrix n k' ℝ} {S₁ : Matrix k k' ℝ}
  {Y₁ : Matrix m n ℝ}

/-- **The K-step of the matrix implicit BUG integrator for a Sylvester-stiff field, against a
reference.** Let `F(t, Z) = M Z + Z N + G(t, Z)` be one-sided Lipschitz with the constant `ℓ` and
`G` be `L`-Lipschitz. With the projector `Q₀ = V₀ V₀ᵀ` onto the old row space, the K-step
result `K₁ V₀ᵀ` of a step from `Y₀ = U₀ S₀ V₀ᵀ` satisfies for all matrices `X₀`, `X₁`

  `(1 - h ℓ) ‖K₁ V₀ᵀ - X₁ Q₀‖ ≤ ‖Y₀ - X₀‖ + ‖(X₁ - X₀ - h F(t₁, X₁)) Q₀‖`
  `    + h ‖X₁ (1 - Q₀) N Q₀‖ + h L ‖X₁ - X₁ Q₀‖`.

The matrix `M` does not occur outside `ℓ` and the defect of the reference; `N` occurs through
its block between the old row space of the numerical solution and its complement, applied to
the rows of `X₁` outside this space. -/
theorem norm_kstep_sub_le_of_sylvester_add
    (hs : IsMatrixImplicitBUGStep (fun t Z => M * Z + Z * N + G t Z) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁
      U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    (hℓ : IsOneSidedLipschitzField (fun t Z => M * Z + Z * N + G t Z) ℓ)
    (hG : IsLipschitzField G L) (X₀ X₁ : Matrix m n ℝ) :
    (1 - h * ℓ) * ‖K₁ * V₀ᵀ - X₁ * (V₀ * V₀ᵀ)‖ ≤
      ‖U₀ * S₀ * V₀ᵀ - X₀‖ +
        ‖(X₁ - X₀ - h • (M * X₁ + X₁ * N + G t₁ X₁)) * (V₀ * V₀ᵀ)‖ +
        h * ‖X₁ * (1 - V₀ * V₀ᵀ) * N * (V₀ * V₀ᵀ)‖ + h * L * ‖X₁ - X₁ * (V₀ * V₀ᵀ)‖ := by
  have hQ : V₀ * V₀ᵀ * (V₀ * V₀ᵀ) = V₀ * V₀ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V₀ᵀ, hs.orthV₀, Matrix.one_mul]
  have hY₀ : rightProj V₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [rightProj_apply, Matrix.mul_assoc (U₀ * S₀), hs.orthV₀, Matrix.mul_one]
  have key := hs.toAbstract.norm_kstep_sub_le_of_add hh hY₀ (X₀ := X₀) (X₁ := X₁)
    (S := fun Z => M * Z + Z * N) (G := G t₁) (L := L) (ℓ := ℓ) (fun _ => rfl)
    (fun z w => by rw [Matrix.mul_sub, Matrix.sub_mul]; abel) (hG t₁ _ _) (hℓ t₁ _ _)
  simp only [rightProj_apply'] at key
  rwa [sylvester_sub_mul_mul_eq hQ] at key

/-- **The L-step of the matrix implicit BUG integrator for a Sylvester-stiff field, against a
reference.** Under the hypotheses of `IsMatrixImplicitBUGStep.norm_kstep_sub_le_of_sylvester_add`
and with the projector `P₀ = U₀ U₀ᵀ` onto the old column space, the L-step result `U₀ L₁ᵀ`
satisfies for all matrices `X₀`, `X₁`

  `(1 - h ℓ) ‖U₀ L₁ᵀ - P₀ X₁‖ ≤ ‖Y₀ - X₀‖ + ‖P₀ (X₁ - X₀ - h F(t₁, X₁))‖`
  `    + h ‖P₀ M (1 - P₀) X₁‖ + h L ‖X₁ - P₀ X₁‖`. -/
theorem norm_lstep_sub_le_of_sylvester_add
    (hs : IsMatrixImplicitBUGStep (fun t Z => M * Z + Z * N + G t Z) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁
      U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    (hℓ : IsOneSidedLipschitzField (fun t Z => M * Z + Z * N + G t Z) ℓ)
    (hG : IsLipschitzField G L) (X₀ X₁ : Matrix m n ℝ) :
    (1 - h * ℓ) * ‖U₀ * L₁ᵀ - U₀ * U₀ᵀ * X₁‖ ≤
      ‖U₀ * S₀ * V₀ᵀ - X₀‖ +
        ‖U₀ * U₀ᵀ * (X₁ - X₀ - h • (M * X₁ + X₁ * N + G t₁ X₁))‖ +
        h * ‖U₀ * U₀ᵀ * M * (1 - U₀ * U₀ᵀ) * X₁‖ + h * L * ‖X₁ - U₀ * U₀ᵀ * X₁‖ := by
  have hP : U₀ * U₀ᵀ * (U₀ * U₀ᵀ) = U₀ * U₀ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U₀ᵀ, hs.orthU₀, Matrix.one_mul]
  have hY₀ : leftProj U₀ (U₀ * S₀ * V₀ᵀ) = U₀ * S₀ * V₀ᵀ := by
    rw [leftProj_apply, Matrix.mul_assoc U₀ S₀, Matrix.mul_assoc U₀ U₀ᵀ,
      ← Matrix.mul_assoc U₀ᵀ U₀, hs.orthU₀, Matrix.one_mul]
  have key := hs.toAbstract.norm_lstep_sub_le_of_add hh hY₀ (X₀ := X₀) (X₁ := X₁)
    (S := fun Z => M * Z + Z * N) (G := G t₁) (L := L) (ℓ := ℓ) (fun _ => rfl)
    (fun z w => by rw [Matrix.mul_sub, Matrix.sub_mul]; abel) (hG t₁ _ _) (hℓ t₁ _ _)
  simp only [leftProj_apply] at key
  rwa [mul_sylvester_sub_mul_eq hP] at key

end IsMatrixImplicitBUGStep

/-! ### Examples -/

/-- **Non-vacuity of `implicitGalerkin_compare_of_add` with an arbitrarily stiff part**: on `ℝ`
with `P = 1`, `S z = -lam z` for any `lam ≥ 0`, `G = 1` (`L = 0`, `ℓ = -lam`), the backward Euler
step `x₁ = (x₀ + 1)/(1 + lam)` of size `h = 1` and any reference states `u₀`, `u₁`. The matrix
forms for `S(Z) = M Z + Z N` with a projector that does not commute with `S` are instantiated
in `LeanDLRA/Research/ImplicitBUGStiffRows.lean`. -/
example {lam : ℝ} (hlam : 0 ≤ lam) (x₀ u₀ u₁ : ℝ) :
    (1 - 1 * -lam) * ‖(x₀ + 1) / (1 + lam) - (1 : ℝ →L[ℝ] ℝ) u₁‖ ≤
      ‖x₀ - u₀‖ + ‖(1 : ℝ →L[ℝ] ℝ) (u₁ - u₀ - (1 : ℝ) • (-(lam * u₁) + 1))‖ +
        1 * ‖(1 : ℝ →L[ℝ] ℝ) (-(lam * (u₁ - (1 : ℝ →L[ℝ] ℝ) u₁)))‖ +
        1 * 0 * ‖u₁ - (1 : ℝ →L[ℝ] ℝ) u₁‖ :=
  implicitGalerkin_compare_of_add (F := fun _ z => -(lam * z) + 1) (S := fun z => -(lam * z))
    (G := fun _ => 1) (t := 0) IsOrthProj.one zero_le_one
    (by
      have h0 : (1 : ℝ) + lam ≠ 0 := by positivity
      change (x₀ + 1) / (1 + lam) = x₀ + (1 : ℝ) • (-(lam * ((x₀ + 1) / (1 + lam))) + 1)
      rw [smul_eq_mul]
      field_simp
      ring)
    (fun _ => rfl) (fun z w => by ring) (by simp)
    (by
      have e : ∀ x y : ℝ, -(lam * x) + 1 - (-(lam * y) + 1) = (-lam) • (x - y) := fun x y => by
        rw [smul_eq_mul]
        ring
      rw [e, real_inner_smul_left, real_inner_self_eq_norm_sq])

end LeanDLRA

import LeanDLRA.Research.ImplicitBUGStiffTwoSided

/-!
# The S-step of the implicit BUG integrator is an energy projection

For the field `F(Z) = -BᵀB Z - Z CᵀC` (two symmetric negative semidefinite matrices of any norm,
one on each side: a discrete heat equation, a Lyapunov equation) the backward Euler step on the
full matrix, `A + h (BᵀB A + A CᵀC) = Y₀`, is the minimiser of a quadratic functional whose
second-order part is the energy

  `‖Z‖² + h ‖B Z‖² + h ‖Z Cᵀ‖²`.

The S-step of the BUG integrator with backward Euler substeps is the Galerkin equation of the
same problem on the space `{U₁ G V₁ᵀ}` of the new bases. Hence, whatever the bases are (the
fixed-rank choice `U₁ = orth K₁`, the augmented choice `U₁ = orth [K₁, U₀]`, or any other),
`U₁ S₁ V₁ᵀ` is the best approximation of the full backward Euler step `A` in this space, in the
energy norm: for every `G`

  `E(U₁ S₁ V₁ᵀ - A) + E(U₁ G V₁ᵀ - U₁ S₁ V₁ᵀ) = E(U₁ G V₁ᵀ - A)`.

The stiffness enters the error of the step only through the energy distance of `A` to the tensor
space of the new bases; no bound of `B` or `C` is used. The K- and L-steps enter only through
the bases.

## Main results

* `IsMatrixImplicitBUGStep.inner_sstep_mul_mul_transpose`: the Galerkin equation of the S-step,
  for every field.
* `IsMatrixImplicitBUGStep.sq_norm_sstep_eq_inner`: `‖U₁ S₁ V₁ᵀ‖² = ⟪Y₀ + h F(U₁ S₁ V₁ᵀ),
  U₁ S₁ V₁ᵀ⟫`, for every field.
* `IsMatrixImplicitBUGStep.energy_sub_add_energy_sub_eq_of_sylvester`: the identity above.
* `IsMatrixImplicitBUGStep.energy_sub_le_of_sylvester`: the best approximation property.
* `IsMatrixImplicitBUGStep.energy_eq_inner_of_sylvester`,
  `IsMatrixImplicitBUGStep.norm_sstep_le_of_sylvester`: `E(U₁ S₁ V₁ᵀ) = ⟪Y₀, U₁ S₁ V₁ᵀ⟫` and
  `‖U₁ S₁ V₁ᵀ‖ ≤ ‖Y₀‖`.
* `exists_add_smul_sylvester_eq`: the backward Euler step on the full matrix exists for `h ≥ 0`.
* `exists_eq_transpose_mul_add_smul_mul`: the S-step is solvable for every linear dissipative
  field and `h ≥ 0`.
* `IsMatrixImplicitBUGStep.exists_forall_energy_sub_le_of_sylvester`: both together.

## References

* [CerutiLubich2022] for the BUG integrator; backward Euler substeps as in arXiv 2610.18419.
-/

open scoped Matrix RealInnerProductSpace LeanDLRA.Frobenius

open Matrix

namespace LeanDLRA

namespace ImplicitBUGEnergyProjection

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q]

/-- A factor on each side moves to the other argument: `⟪Z, U G Vᵀ⟫ = ⟪Uᵀ Z V, G⟫`. -/
private theorem inner_mul_mul_transpose (Z : Matrix m n ℝ) (U : Matrix m k₁ ℝ)
    (G : Matrix k₁ k₂ ℝ) (V : Matrix n k₂ ℝ) : ⟪Z, U * G * Vᵀ⟫ = ⟪Uᵀ * Z * V, G⟫ := by
  rw [Frobenius.inner_mul_right', Matrix.transpose_transpose, Frobenius.inner_mul_left',
    Matrix.mul_assoc]

/-- The Galerkin equation: if `S = Uᵀ Z V` with orthonormal `U`, `V`, then `U S Vᵀ - Z` is
orthogonal to every `U G Vᵀ`. -/
private theorem inner_galerkin [DecidableEq k₁] [DecidableEq k₂] {U : Matrix m k₁ ℝ}
    {V : Matrix n k₂ ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {Z : Matrix m n ℝ}
    {S : Matrix k₁ k₂ ℝ} (hS : S = Uᵀ * Z * V) (G : Matrix k₁ k₂ ℝ) :
    ⟪U * S * Vᵀ, U * G * Vᵀ⟫ = ⟪Z, U * G * Vᵀ⟫ := by
  have e : Uᵀ * (U * S * Vᵀ) * V = S := by
    rw [show Uᵀ * (U * S * Vᵀ) * V = (Uᵀ * U) * S * (Vᵀ * V) by simp only [Matrix.mul_assoc],
      hU, hV, Matrix.one_mul, Matrix.mul_one]
  rw [inner_mul_mul_transpose Z, ← hS, inner_mul_mul_transpose, e]

/-- `⟪BᵀB Z, W⟫ = ⟪B Z, B W⟫`. -/
private theorem inner_gram_mul (B : Matrix p m ℝ) (Z W : Matrix m n ℝ) :
    ⟪Bᵀ * B * Z, W⟫ = ⟪B * Z, B * W⟫ := by
  rw [Matrix.mul_assoc, Frobenius.inner_mul_left, Matrix.transpose_transpose]

/-- `⟪Z CᵀC, W⟫ = ⟪Z Cᵀ, W Cᵀ⟫`. -/
private theorem inner_mul_gram (C : Matrix q n ℝ) (Z W : Matrix m n ℝ) :
    ⟪Z * (Cᵀ * C), W⟫ = ⟪Z * Cᵀ, W * Cᵀ⟫ := by
  rw [← Matrix.mul_assoc, Frobenius.inner_mul_right]

/-- The energy of a sum of two matrices that are orthogonal in the energy inner product. -/
private theorem energy_add_energy_eq {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}
    {X W A : Matrix m n ℝ}
    (horth : ⟪X - A, W - X⟫ + h * ⟪B * (X - A), B * (W - X)⟫ +
      h * ⟪(X - A) * Cᵀ, (W - X) * Cᵀ⟫ = 0) :
    (‖X - A‖ ^ 2 + h * ‖B * (X - A)‖ ^ 2 + h * ‖(X - A) * Cᵀ‖ ^ 2) +
      (‖W - X‖ ^ 2 + h * ‖B * (W - X)‖ ^ 2 + h * ‖(W - X) * Cᵀ‖ ^ 2) =
      ‖W - A‖ ^ 2 + h * ‖B * (W - A)‖ ^ 2 + h * ‖(W - A) * Cᵀ‖ ^ 2 := by
  have e : W - A = (X - A) + (W - X) := by abel
  rw [e, Matrix.mul_add, Matrix.add_mul, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
  linear_combination (-2 : ℝ) * horth

/-- The energy inner product with the full backward Euler step is the inner product with the
right-hand side. -/
private theorem inner_resolvent {B : Matrix p m ℝ} {C : Matrix q n ℝ} {h : ℝ}
    {A Y : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = Y) (W : Matrix m n ℝ) :
    ⟪A, W⟫ + h * ⟪B * A, B * W⟫ + h * ⟪A * Cᵀ, W * Cᵀ⟫ = ⟪Y, W⟫ := by
  rw [← hA, inner_add_left, real_inner_smul_left, inner_add_left, inner_gram_mul,
    inner_mul_gram]
  ring

end ImplicitBUGEnergyProjection

open ImplicitBUGEnergyProjection

section Resolvent

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-- **The backward Euler step on the full matrix exists**: for `h ≥ 0` and every `Y` the
equation `A + h (BᵀB A + A CᵀC) = Y` has a solution, whatever the size of `B` and `C`. -/
theorem exists_add_smul_sylvester_eq (B : Matrix p m ℝ) (C : Matrix q n ℝ) {h : ℝ} (hh : 0 ≤ h)
    (Y : Matrix m n ℝ) : ∃ A : Matrix m n ℝ, A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = Y := by
  let T : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ :=
    { toFun := fun A => A + h • (Bᵀ * B * A + A * (Cᵀ * C))
      map_add' := fun A A' => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add,
          smul_comm h c] }
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    have hA' : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = 0 := hA
    have h1 := inner_resolvent hA' A
    rw [inner_zero_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at h1
    have h2 := mul_nonneg hh (sq_nonneg ‖B * A‖)
    have h3 := mul_nonneg hh (sq_nonneg ‖A * Cᵀ‖)
    have h4 : ‖A‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
  obtain ⟨A, hA⟩ := (LinearMap.injective_iff_surjective.1 hinj) Y
  exact ⟨A, hA⟩

/-- **The S-step is solvable for every linear dissipative field**: for a linear `Φ` with
`⟪Φ Z, Z⟫ ≤ 0`, `h ≥ 0`, orthonormal `U`, `V` (of any sizes) and every `Y` there is `S` with
`S = Uᵀ (Y + h Φ(U S Vᵀ)) V`. No bound of `Φ` enters. -/
theorem exists_eq_transpose_mul_add_smul_mul {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k₁] [DecidableEq k₂] (Φ : Matrix m n ℝ →ₗ[ℝ] Matrix m n ℝ)
    (hdiss : ∀ Z, ⟪Φ Z, Z⟫ ≤ 0) {h : ℝ} (hh : 0 ≤ h) {U : Matrix m k₁ ℝ} {V : Matrix n k₂ ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (Y : Matrix m n ℝ) :
    ∃ S : Matrix k₁ k₂ ℝ, S = Uᵀ * (Y + h • Φ (U * S * Vᵀ)) * V := by
  let T : Matrix k₁ k₂ ℝ →ₗ[ℝ] Matrix k₁ k₂ ℝ :=
    { toFun := fun S => S - h • (Uᵀ * Φ (U * S * Vᵀ) * V)
      map_add' := fun S S' => by
        simp only [Matrix.mul_add, Matrix.add_mul, map_add, smul_add]
        abel
      map_smul' := fun c S => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply, smul_sub,
          smul_comm h c] }
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro S hS
    have hS0 : S - h • (Uᵀ * Φ (U * S * Vᵀ) * V) = 0 := hS
    have hS' : S = Uᵀ * (h • Φ (U * S * Vᵀ)) * V := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      exact sub_eq_zero.1 hS0
    have h1 := inner_galerkin hU hV hS' S
    rw [real_inner_self_eq_norm_sq, real_inner_smul_left] at h1
    have h2 := mul_nonpos_of_nonneg_of_nonpos hh (hdiss (U * S * Vᵀ))
    have h3 : ‖U * S * Vᵀ‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have h4 : U * S * Vᵀ = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    have h5 : S = Uᵀ * (U * S * Vᵀ) * V := by
      rw [show Uᵀ * (U * S * Vᵀ) * V = (Uᵀ * U) * S * (Vᵀ * V) by simp only [Matrix.mul_assoc],
        hU, hV, Matrix.one_mul, Matrix.mul_one]
    rw [h5, h4, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨S, hS⟩ := (LinearMap.injective_iff_surjective.1 hinj) (Uᵀ * Y * V)
  have hS0 : S - h • (Uᵀ * Φ (U * S * Vᵀ) * V) = Uᵀ * Y * V := hS
  refine ⟨S, ?_⟩
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact sub_eq_iff_eq_add.1 hS0

end Resolvent

section Step

variable {m n k₁ k₂ p q : Type*} [Fintype m] [Fintype n] [Fintype k₁] [Fintype k₂] [Fintype p]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq k₁] [DecidableEq k₂] {r : ℕ}
  {F : ℝ → Matrix m n ℝ → Matrix m n ℝ} {B : Matrix p m ℝ} {C : Matrix q n ℝ} {ε τ ϑ t₁ h : ℝ}
  {U₀ : Matrix m (Fin r) ℝ} {S₀ : Matrix (Fin r) (Fin r) ℝ} {V₀ : Matrix n (Fin r) ℝ}
  {K₁ : Matrix m (Fin r) ℝ} {L₁ : Matrix n (Fin r) ℝ} {U₁ : Matrix m k₁ ℝ} {V₁ : Matrix n k₂ ℝ}
  {S₁ : Matrix k₁ k₂ ℝ} {Y₁ : Matrix m n ℝ}

/-- **The Galerkin equation of the S-step**, for every field and every choice of the new bases:
`U₁ S₁ V₁ᵀ - (Y₀ + h F(t₁, U₁ S₁ V₁ᵀ))` is orthogonal to every matrix `U₁ G V₁ᵀ`. -/
theorem IsMatrixImplicitBUGStep.inner_sstep_mul_mul_transpose
    (hs : IsMatrixImplicitBUGStep F ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁)
    (G : Matrix k₁ k₂ ℝ) :
    ⟪U₁ * S₁ * V₁ᵀ, U₁ * G * V₁ᵀ⟫ =
      ⟪U₀ * S₀ * V₀ᵀ + h • F t₁ (U₁ * S₁ * V₁ᵀ), U₁ * G * V₁ᵀ⟫ :=
  inner_galerkin hs.orthU₁ hs.orthV₁ hs.sstep G

/-- **The energy identity of the S-step**, for every field:
`‖U₁ S₁ V₁ᵀ‖² = ⟪Y₀ + h F(t₁, U₁ S₁ V₁ᵀ), U₁ S₁ V₁ᵀ⟫`. -/
theorem IsMatrixImplicitBUGStep.sq_norm_sstep_eq_inner
    (hs : IsMatrixImplicitBUGStep F ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) :
    ‖U₁ * S₁ * V₁ᵀ‖ ^ 2 =
      ⟪U₀ * S₀ * V₀ᵀ + h • F t₁ (U₁ * S₁ * V₁ᵀ), U₁ * S₁ * V₁ᵀ⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  exact hs.inner_sstep_mul_mul_transpose S₁

/-- The error of the S-step against the backward Euler step on the full matrix is orthogonal,
in the energy inner product, to the tensor space of the new bases. -/
private theorem ImplicitBUGEnergyProjection.energy_inner_sub_eq_zero
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    (G : Matrix k₁ k₂ ℝ) :
    ⟪U₁ * S₁ * V₁ᵀ - A, U₁ * G * V₁ᵀ⟫ +
        h * ⟪B * (U₁ * S₁ * V₁ᵀ - A), B * (U₁ * G * V₁ᵀ)⟫ +
        h * ⟪(U₁ * S₁ * V₁ᵀ - A) * Cᵀ, U₁ * G * V₁ᵀ * Cᵀ⟫ = 0 := by
  have h1 := hs.inner_sstep_mul_mul_transpose G
  beta_reduce at h1
  rw [inner_add_left, real_inner_smul_left, inner_sub_left, inner_neg_left, inner_gram_mul,
    inner_mul_gram] at h1
  have h2 := inner_resolvent hA (U₁ * G * V₁ᵀ)
  rw [Matrix.mul_sub, Matrix.sub_mul, inner_sub_left, inner_sub_left, inner_sub_left]
  linear_combination h1 - h2

/-- **The S-step is the energy projection of the full backward Euler step.** Let
`F(Z) = -BᵀB Z - Z CᵀC` and `A + h (BᵀB A + A CᵀC) = Y₀` (backward Euler on the full matrix).
For a step of the implicit BUG integrator with any new bases `U₁`, `V₁` and every `G`, with
`E(Z) = ‖Z‖² + h ‖B Z‖² + h ‖Z Cᵀ‖²`,

  `E(U₁ S₁ V₁ᵀ - A) + E(U₁ G V₁ᵀ - U₁ S₁ V₁ᵀ) = E(U₁ G V₁ᵀ - A)`.

No bound of `B`, `C` and no sign of `h` is used. -/
theorem IsMatrixImplicitBUGStep.energy_sub_add_energy_sub_eq_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    (G : Matrix k₁ k₂ ℝ) :
    (‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2) +
      (‖U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ‖ ^ 2 + h * ‖B * (U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ)‖ ^ 2 +
        h * ‖(U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ) * Cᵀ‖ ^ 2) =
      ‖U₁ * G * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * G * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * G * V₁ᵀ - A) * Cᵀ‖ ^ 2 := by
  refine energy_add_energy_eq ?_
  have e : U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ = U₁ * (G - S₁) * V₁ᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [e]
  exact energy_inner_sub_eq_zero hs hA (G - S₁)

/-- **Best approximation in the energy norm.** In the setting of
`IsMatrixImplicitBUGStep.energy_sub_add_energy_sub_eq_of_sylvester` with `h ≥ 0`: the result of
the S-step is at least as close to the full backward Euler step `A`, in the energy
`E(Z) = ‖Z‖² + h ‖B Z‖² + h ‖Z Cᵀ‖²`, as every other matrix `U₁ G V₁ᵀ` of the new bases. -/
theorem IsMatrixImplicitBUGStep.energy_sub_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h)
    {A : Matrix m n ℝ} (hA : A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ)
    (G : Matrix k₁ k₂ ℝ) :
    ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2 ≤
      ‖U₁ * G * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * G * V₁ᵀ - A)‖ ^ 2 +
        h * ‖(U₁ * G * V₁ᵀ - A) * Cᵀ‖ ^ 2 := by
  rw [← hs.energy_sub_add_energy_sub_eq_of_sylvester hA G]
  have h1 := mul_nonneg hh (sq_nonneg ‖B * (U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ)‖)
  have h2 := mul_nonneg hh (sq_nonneg ‖(U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ) * Cᵀ‖)
  have h3 := sq_nonneg ‖U₁ * G * V₁ᵀ - U₁ * S₁ * V₁ᵀ‖
  linarith

/-- **The energy of the S-step result**: for `F(Z) = -BᵀB Z - Z CᵀC` and any new bases,
`‖U₁ S₁ V₁ᵀ‖² + h ‖B U₁ S₁ V₁ᵀ‖² + h ‖U₁ S₁ V₁ᵀ Cᵀ‖² = ⟪Y₀, U₁ S₁ V₁ᵀ⟫`. -/
theorem IsMatrixImplicitBUGStep.energy_eq_inner_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) :
    ‖U₁ * S₁ * V₁ᵀ‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ)‖ ^ 2 + h * ‖U₁ * S₁ * V₁ᵀ * Cᵀ‖ ^ 2 =
      ⟪U₀ * S₀ * V₀ᵀ, U₁ * S₁ * V₁ᵀ⟫ := by
  have h1 := hs.sq_norm_sstep_eq_inner
  beta_reduce at h1
  rw [inner_add_left, real_inner_smul_left, inner_sub_left, inner_neg_left, inner_gram_mul,
    inner_mul_gram, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  linear_combination h1

/-- **Norm stability of the S-step** for `F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0`, any new bases:
`‖U₁ S₁ V₁ᵀ‖ ≤ ‖Y₀‖`, uniformly in `B` and `C`. -/
theorem IsMatrixImplicitBUGStep.norm_sstep_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h) :
    ‖U₁ * S₁ * V₁ᵀ‖ ≤ ‖U₀ * S₀ * V₀ᵀ‖ := by
  have h1 := hs.energy_eq_inner_of_sylvester
  have h2 := real_inner_le_norm (U₀ * S₀ * V₀ᵀ) (U₁ * S₁ * V₁ᵀ)
  have h3 := mul_nonneg hh (sq_nonneg ‖B * (U₁ * S₁ * V₁ᵀ)‖)
  have h4 := mul_nonneg hh (sq_nonneg ‖U₁ * S₁ * V₁ᵀ * Cᵀ‖)
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg (U₀ * S₀ * V₀ᵀ), norm_nonneg (U₁ * S₁ * V₁ᵀ)]

/-- **The S-step is at least as good as every matrix of the new bases, against the backward
Euler step on the full matrix.** For `F(Z) = -BᵀB Z - Z CᵀC`, `h ≥ 0` and any new bases the
backward Euler step `A` on the full matrix from `Y₀` exists, and for every `G`

  `E(U₁ S₁ V₁ᵀ - A) ≤ E(U₁ G V₁ᵀ - A)`,  `E(Z) = ‖Z‖² + h ‖B Z‖² + h ‖Z Cᵀ‖²`. -/
theorem IsMatrixImplicitBUGStep.exists_forall_energy_sub_le_of_sylvester
    (hs : IsMatrixImplicitBUGStep (fun (_ : ℝ) (Z : Matrix m n ℝ) =>
      -(Bᵀ * B * Z) - Z * (Cᵀ * C)) ε τ ϑ t₁ h U₀ S₀ V₀ K₁ L₁ U₁ V₁ S₁ Y₁) (hh : 0 ≤ h) :
    ∃ A : Matrix m n ℝ, A + h • (Bᵀ * B * A + A * (Cᵀ * C)) = U₀ * S₀ * V₀ᵀ ∧
      ∀ G : Matrix k₁ k₂ ℝ,
        ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
            h * ‖(U₁ * S₁ * V₁ᵀ - A) * Cᵀ‖ ^ 2 ≤
          ‖U₁ * G * V₁ᵀ - A‖ ^ 2 + h * ‖B * (U₁ * G * V₁ᵀ - A)‖ ^ 2 +
            h * ‖(U₁ * G * V₁ᵀ - A) * Cᵀ‖ ^ 2 := by
  obtain ⟨A, hA⟩ := exists_add_smul_sylvester_eq B C hh (U₀ * S₀ * V₀ᵀ)
  exact ⟨A, hA, fun G => hs.energy_sub_le_of_sylvester hh hA G⟩

end Step

section Example

/-- The hypotheses hold for a family of `2 × 2` steps of rank `1` with an arbitrary stiffness
`lam ≥ 0` on both sides: `B = C = (0, √lam)` (so `-BᵀB = -CᵀC = diag(0, -lam)`), start value
`(c, s)ᵀ (c, s)`; a step exists for every `h ≥ 0`. -/
example {h lam c s : ℝ} (hh : 0 ≤ h) (hlam : 0 ≤ lam) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ (U₁ V₁ : Matrix (Fin 2) (Fin 1) ℝ) (S₁ : Matrix (Fin 1) (Fin 1) ℝ)
      (A : Matrix (Fin 2) (Fin 2) ℝ),
      A + h • ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] * A +
        A * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam])) =
        (!![c; s] : Matrix (Fin 2) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) * !![c; s]ᵀ ∧
      ∀ G : Matrix (Fin 1) (Fin 1) ℝ,
        ‖U₁ * S₁ * V₁ᵀ - A‖ ^ 2 +
            h * ‖(!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ) * (U₁ * S₁ * V₁ᵀ - A)‖ ^ 2 +
            h * ‖(U₁ * S₁ * V₁ᵀ - A) * (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ‖ ^ 2 ≤
          ‖U₁ * G * V₁ᵀ - A‖ ^ 2 +
            h * ‖(!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ) * (U₁ * G * V₁ᵀ - A)‖ ^ 2 +
            h * ‖(U₁ * G * V₁ᵀ - A) * (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ‖ ^ 2 := by
  obtain ⟨K₁, L₁, U₁, V₁, S₁, Y₁, ε, hs⟩ :=
    StiffTwoSidedExample.exists_isMatrixImplicitBUGStep hh hlam hcs 0
  have hC : (!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] = -!![0, 0; 0, -lam] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Real.mul_self_sqrt hlam]
  have hF : (fun (_ : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) =>
      !![0, 0; 0, -lam] * Z + Z * !![0, 0; 0, -lam]) = fun _ Z =>
      -((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam] * Z) -
        Z * ((!![0, √lam] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ * !![0, √lam]) := by
    funext _ Z
    rw [hC, Matrix.neg_mul, neg_neg, Matrix.mul_neg, sub_neg_eq_add]
  rw [hF] at hs
  obtain ⟨A, hA, hmin⟩ := hs.exists_forall_energy_sub_le_of_sylvester hh
  exact ⟨U₁, V₁, S₁, A, hA, hmin⟩

end Example

end LeanDLRA

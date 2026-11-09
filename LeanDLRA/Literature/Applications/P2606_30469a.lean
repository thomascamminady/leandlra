import Mathlib
import LeanDLRA.Matrix.Projectors

/-!
# Complex-matrix ODE results of arXiv 2606.30469 (structure-preserving DLRA for guided waves)

The module formalizes the complex-matrix ODE facts behind the symplectic dynamical low-rank
approximation of the paper. Lemma 5.1 says that `Uᴴ Ω U` is constant along the left-basis
flow `U̇ = -i (I - U Uᴴ) Ω U` when `Ω` is Hermitian. Sec. 7.2 says that the error
`D = Z - U Zᵣ` between the full flow and the lifted reduced flow satisfies `Ḋ = -i Ω D`, so
`Dᴴ D` and the Frobenius norm of `D` are constant; the right-hand side is
`‖Z(TL) - Ur Urᴴ Al Zl(TL)‖`, using the initial condition (6.5). The recombination check of
Sec. 5.3 (after (5.13), pp. 12-13) says that `Z(t) = U(t) Zᵣ(t)` when `Z(TL) = Ur Zᵣ(TL)`; it is
proved here from the ODEs, without the exponential formulas (5.11) and (5.13). Prop. 3.1 says
that `z = S u + i Ω⁻¹ S u̇` with `S² = M` and `Ω² = S⁻¹ K S⁻¹` solves
`ż = -i Ω z + i Ω⁻¹ S⁻¹ f`, and that `zᴴ z` and `‖z‖` are constant when `f = 0`.

Deviations (all make the statements more general): `S` is any invertible matrix with `S² = M`
(not necessarily `M^{1/2}`), any Hermitian invertible `Ω` with `Ω² = S⁻¹ K S⁻¹` is allowed (so
positive definiteness of `Ω`, `M` and `K` is not used), `U(t)` need not have orthonormal columns,
and the data are complex, which includes the paper's real case.

Not formalized: the explicit exponential form (5.11) of Thm. 5.2 (it needs the matrix exponential),
the construction of `Ω` as a square root, the bound of Sec. 7.1, the triangle-inequality and
principal-angle bound in the second half of Sec. 7.2, and (7.1) of Sec. 7.3. The paper does not
fix a norm in Sec. 7.2,
so the Frobenius norm and the Gram identity `Dᴴ D = const` are both stated. Calculus is entrywise:
`MatHasDerivWithinAt` says that each entry has the stated derivative on the set, and solutions live
on `Icc a b` as in `LeanDLRA.Foundations`.

Core reuse: `normal_proj_real` relates the complex normal projector `1 - Ū Ūᴴ` on real data to the
core `LeanDLRA.leftProj` (through `LeanDLRA.one_sub_leftProj_apply`). The core has no complex
matrix objects, so the complex solutions, `frobNorm`, `phaseVec` and `MatHasDerivWithinAt` are
defined here.
-/

open Set Filter Topology Finset
open scoped Matrix

namespace LeanDLRA.Literature.P2606_30469

def MatHasDerivWithinAt {p q : Type*} (A : ℝ → Matrix p q ℂ) (A' : Matrix p q ℂ)
    (s : Set ℝ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivWithinAt (fun τ => A τ i j) (A' i j) s t

section Calculus

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {p q k : Type*} {s : Set ℝ} {t : ℝ}

lemma MatHasDerivWithinAt.mul [Fintype q] {A : ℝ → Matrix p q ℂ} {B : ℝ → Matrix q k ℂ}
    {A' : Matrix p q ℂ} {B' : Matrix q k ℂ}
    (hA : MatHasDerivWithinAt A A' s t) (hB : MatHasDerivWithinAt B B' s t) :
    MatHasDerivWithinAt (fun τ => A τ * B τ) (A' * B t + A t * B') s t := by
  intro i j
  have h := HasDerivWithinAt.sum (u := (univ : Finset q))
    (A := fun x τ => A τ i x * B τ x j)
    (A' := fun x => A' i x * B t x j + A t i x * B' x j)
    (fun x _ => (hA i x).mul (hB x j))
  convert h using 1
  · funext τ; simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib]

lemma MatHasDerivWithinAt.const (C : Matrix p q ℂ) : MatHasDerivWithinAt (fun _ => C) 0 s t :=
  fun i j => hasDerivWithinAt_const t s (C i j)

lemma MatHasDerivWithinAt.conjTranspose {A : ℝ → Matrix p q ℂ} {A' : Matrix p q ℂ}
    (hA : MatHasDerivWithinAt A A' s t) : MatHasDerivWithinAt (fun τ => (A τ)ᴴ) (A')ᴴ s t :=
  fun i j => (hA j i).star

lemma MatHasDerivWithinAt.congr_deriv {A : ℝ → Matrix p q ℂ} {A' B' : Matrix p q ℂ}
    (hA : MatHasDerivWithinAt A A' s t) (e : A' = B') : MatHasDerivWithinAt A B' s t :=
  e ▸ hA

lemma MatHasDerivWithinAt.smul {A : ℝ → Matrix p q ℂ} {A' : Matrix p q ℂ} (c : ℂ)
    (hA : MatHasDerivWithinAt A A' s t) :
    MatHasDerivWithinAt (fun τ => c • A τ) (c • A') s t :=
  fun i j => by simpa using (hA i j).const_mul c

lemma MatHasDerivWithinAt.add {A B : ℝ → Matrix p q ℂ} {A' B' : Matrix p q ℂ}
    (hA : MatHasDerivWithinAt A A' s t) (hB : MatHasDerivWithinAt B B' s t) :
    MatHasDerivWithinAt (fun τ => A τ + B τ) (A' + B') s t :=
  fun i j => (hA i j).add (hB i j)

lemma MatHasDerivWithinAt.sub {A B : ℝ → Matrix p q ℂ} {A' B' : Matrix p q ℂ}
    (hA : MatHasDerivWithinAt A A' s t) (hB : MatHasDerivWithinAt B B' s t) :
    MatHasDerivWithinAt (fun τ => A τ - B τ) (A' - B') s t :=
  fun i j => (hA i j).sub (hB i j)

lemma MatHasDerivWithinAt.const_mul {A : ℝ → Matrix p q ℂ} {A' : Matrix p q ℂ} (C : Matrix k p ℂ)
    [Fintype p] (hA : MatHasDerivWithinAt A A' s t) :
    MatHasDerivWithinAt (fun τ => C * A τ) (C * A') s t :=
  ((MatHasDerivWithinAt.const (s := s) (t := t) C).mul hA).congr_deriv (by simp)

/-- A matrix function with zero derivative on `[a, b]` is constant there. -/
lemma matConst_of_deriv {X X' : ℝ → Matrix p q ℂ} {a b : ℝ}
    (hX : ∀ t ∈ Icc a b, MatHasDerivWithinAt X (X' t) (Icc a b) t)
    (h0 : ∀ t ∈ Icc a b, X' t = 0) : ∀ t ∈ Icc a b, X t = X a := by
  intro t ht
  ext i j
  have hc := constant_of_has_deriv_right_zero (f := fun τ => X τ i j)
    (a := a) (b := b) (fun τ hτ => (hX τ hτ i j).continuousWithinAt)
    (fun τ hτ => by
      have h := hX τ (Set.Ico_subset_Icc_self hτ) i j
      rw [h0 τ (Set.Ico_subset_Icc_self hτ)] at h
      exact h.mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hτ.2) (Icc_subset_Icc hτ.1 le_rfl)))
    t ht
  simpa using hc

variable {n r : Type*} [Fintype n] [DecidableEq n]

/-- Lemma 5.1 (matrix algebra): the derivative of `Uᴴ Ω U` along `U' = -i (I - U Uᴴ) Ω U` is
zero when `Ω` is Hermitian. -/
private lemma lemma51_alg {Ω : Matrix n n ℂ} (hΩ : Ωᴴ = Ω) [Fintype r] (U : Matrix n r ℂ) :
    ((-Complex.I) • ((1 - U * Uᴴ) * Ω * U))ᴴ * Ω * U
      + Uᴴ * Ω * ((-Complex.I) • ((1 - U * Uᴴ) * Ω * U)) = 0 := by
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, hΩ, star_neg,
    Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, Matrix.smul_mul]
  module

/-- Lemma 5.1 of arXiv 2606.30469. Along any solution of
`U̇ = -i (I - U Uᴴ) Ω U` on `[a, b]`, the reduced matrix `Uᴴ Ω U` is constant, provided `Ω`
is Hermitian. -/
theorem reduced_matrix_const {Ω : Matrix n n ℂ} (hΩ : Ωᴴ = Ω) [Fintype r] {U : ℝ → Matrix n r ℂ}
    {a b : ℝ}
    (hU : ∀ t ∈ Icc a b,
      MatHasDerivWithinAt U ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, (U t)ᴴ * Ω * U t = (U a)ᴴ * Ω * U a := by
  refine matConst_of_deriv (X' := fun t => ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t))ᴴ * Ω
    * U t + (U t)ᴴ * Ω * ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t))) ?_ ?_
  · intro t ht
    exact ((((hU t ht).conjTranspose).mul (MatHasDerivWithinAt.const Ω)).mul (hU t ht))
      |>.congr_deriv (by simp)
  · intro t _
    exact lemma51_alg hΩ (U t)

/-- Lemma (Gram matrix): if `Ḋ = -i Ω D` with `Ω` Hermitian, then `Dᴴ D` is constant. -/
private lemma gram_const_of_ode {Ω : Matrix n n ℂ} (hΩ : Ωᴴ = Ω) {m : Type*} [Fintype m]
    {D : ℝ → Matrix n m ℂ} {a b : ℝ}
    (hD : ∀ t ∈ Icc a b, MatHasDerivWithinAt D ((-Complex.I) • (Ω * D t)) (Icc a b) t) :
    ∀ t ∈ Icc a b, (D t)ᴴ * D t = (D a)ᴴ * D a := by
  refine matConst_of_deriv (X' := fun t => ((-Complex.I) • (Ω * D t))ᴴ * D t
    + (D t)ᴴ * ((-Complex.I) • (Ω * D t))) ?_ ?_
  · intro t ht
    exact ((hD t ht).conjTranspose.mul (hD t ht)).congr_deriv rfl
  · intro t _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hΩ, star_neg,
      Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    module

/-- Frobenius norm of a complex matrix. -/
noncomputable def frobNorm {p q : Type*} [Fintype p] [Fintype q] (A : Matrix p q ℂ) : ℝ :=
  √(∑ i, ∑ j, ‖A i j‖ ^ 2)

private lemma sum_norm_sq_cast {m : Type*} [Fintype m] (A : Matrix n m ℂ) :
    ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Aᴴ * A) := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul', Finset.sum_comm (γ := m)]

private lemma frobNorm_eq_of_gram {m : Type*} [Fintype m] {A B : Matrix n m ℂ}
    (h : Aᴴ * A = Bᴴ * B) : frobNorm A = frobNorm B := by
  unfold frobNorm
  congr 1
  have hA := sum_norm_sq_cast A
  have hB := sum_norm_sq_cast B
  rw [h, ← hB] at hA
  exact_mod_cast hA

private lemma eq_zero_of_gram_zero {m : Type*} [Fintype m] {A : Matrix n m ℂ}
    (h : Aᴴ * A = 0) : A = 0 := by
  have hs : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 0 := by
    have := sum_norm_sq_cast A
    rw [h, Matrix.trace_zero] at this
    exact_mod_cast this
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖)).1 hs i (Finset.mem_univ _)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖A i j‖)).1 hi j
    (Finset.mem_univ _)
  simpa using hj

/-- The error `D = Z - U Zᵣ` between the full solution and the lifted reduced solution satisfies
`Ḋ = -i Ω D` on `[TL, T]`, using the left-basis ODE and Lemma 5.1 (for `Uᴴ Ω U = Ω_r`). -/
private lemma error_ode {TL T : ℝ} {m : Type*} [Fintype m] [Fintype r] {Ω : Matrix n n ℂ}
    (hΩ : Ωᴴ = Ω) {Z : ℝ → Matrix n m ℂ} {U : ℝ → Matrix n r ℂ} {Zr : ℝ → Matrix r m ℂ}
    {Ur : Matrix n r ℂ}
    (hZ : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Z ((-Complex.I) • (Ω * Z t)) (Icc TL T) t)
    (hU : ∀ t ∈ Icc TL T,
      MatHasDerivWithinAt U ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t)) (Icc TL T) t)
    (hU0 : U TL = Ur)
    (hZr : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Zr ((-Complex.I) • (Ur ᴴ * Ω * Ur * Zr t))
      (Icc TL T) t) :
    ∀ t ∈ Icc TL T, MatHasDerivWithinAt (fun τ => Z τ - U τ * Zr τ)
      ((-Complex.I) • (Ω * (Z t - U t * Zr t))) (Icc TL T) t := by
  intro t ht
  refine ((hZ t ht).sub ((hU t ht).mul (hZr t ht))).congr_deriv ?_
  have hc : (U t)ᴴ * Ω * U t = Ur ᴴ * Ω * Ur := by
    have := reduced_matrix_const hΩ hU t ht
    rwa [hU0] at this
  have hU' : (1 - U t * (U t)ᴴ) * Ω * U t = Ω * U t - U t * ((U t)ᴴ * Ω * U t) := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [hU', hc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, smul_sub]
  module

/-- **Sec. 7.2 (isometry identity)** of arXiv 2606.30469. On `[TL, T]`, with the full solution `Z`
  of `Ż = -i Ω Z`, the left-basis solution `U` of `U̇ = -i (I - U Uᴴ) Ω U` with `U(TL) = Ur`,
  and the reduced solution `Zᵣ` of `Żᵣ = -i Ωᵣ Zᵣ` with `Ωᵣ = Urᴴ Ω Ur` and `Zᵣ(TL) = Urᴴ Al
  Zl`, the propagation error `D(t) = Z(t) - U(t) Zᵣ(t)` is constant in time. Precisely, `Dᴴ D`
  is constant, which gives `‖D(t)‖ = ‖D(TL)‖` for the Frobenius norm and for any norm depending
  only on `Dᴴ D` (the paper does not fix the norm). The right-hand side is `‖Z(TL) - Ur Urᴴ Al
  Zl‖` as stated in the paper. -/
theorem propagation_error_const {TL T : ℝ} {m l : Type*} [Fintype m] [Fintype r] [Fintype l]
    {Ω : Matrix n n ℂ} (hΩ : Ωᴴ = Ω)
    {Z : ℝ → Matrix n m ℂ} {U : ℝ → Matrix n r ℂ} {Zr : ℝ → Matrix r m ℂ}
    {Ur : Matrix n r ℂ} {Al : Matrix n l ℂ} {Zl : Matrix l m ℂ}
    (hZ : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Z ((-Complex.I) • (Ω * Z t)) (Icc TL T) t)
    (hU : ∀ t ∈ Icc TL T,
      MatHasDerivWithinAt U ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t)) (Icc TL T) t)
    (hU0 : U TL = Ur)
    (hZr : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Zr ((-Complex.I) • (Ur ᴴ * Ω * Ur * Zr t))
      (Icc TL T) t)
    (hZr0 : Zr TL = Ur ᴴ * Al * Zl) :
    (∀ t ∈ Icc TL T, (Z t - U t * Zr t)ᴴ * (Z t - U t * Zr t)
        = (Z TL - Ur * (Ur ᴴ * Al * Zl))ᴴ * (Z TL - Ur * (Ur ᴴ * Al * Zl))) ∧
    ∀ t ∈ Icc TL T, frobNorm (Z t - U t * Zr t) = frobNorm (Z TL - Ur * (Ur ᴴ * Al * Zl)) := by
  have hG := gram_const_of_ode hΩ (error_ode hΩ hZ hU hU0 hZr)
  have h0 : Z TL - U TL * Zr TL = Z TL - Ur * (Ur ᴴ * Al * Zl) := by rw [hU0, hZr0]
  have hG' : ∀ t ∈ Icc TL T, (Z t - U t * Zr t)ᴴ * (Z t - U t * Zr t)
      = (Z TL - Ur * (Ur ᴴ * Al * Zl))ᴴ * (Z TL - Ur * (Ur ᴴ * Al * Zl)) := by
    intro t ht
    have := hG t ht
    rwa [h0] at this
  exact ⟨hG', fun t ht => frobNorm_eq_of_gram (hG' t ht)⟩

/-- **Recombination at rank `r`, Sec. 5.3** of arXiv 2606.30469 (the computation after (5.13),
  pp. 12-13). If `Z(TL) = Ur Zᵣ(TL)` (the rank-`r` factorization (5.6), with
  `Zᵣ(TL) = Sr Vrᴴ`), then the product `U(t) Zᵣ(t)` reproduces the full solution `Z(t)` exactly
  on `[TL, T]`, for any solutions `U`, `Zᵣ` of the left-basis ODE (5.8) and the reduced ODE
  (5.12). The paper checks this with the exponential formulas (5.11) and (5.13); here it follows
  from Lemma 5.1 and the ODEs, and (5.11) is not formalized. -/
theorem left_basis_exact {TL T : ℝ} {m : Type*} [Fintype m] [Fintype r] {Ω : Matrix n n ℂ}
    (hΩ : Ωᴴ = Ω)
    {Z : ℝ → Matrix n m ℂ} {U : ℝ → Matrix n r ℂ} {Zr : ℝ → Matrix r m ℂ}
    {Ur : Matrix n r ℂ}
    (hZ : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Z ((-Complex.I) • (Ω * Z t)) (Icc TL T) t)
    (hU : ∀ t ∈ Icc TL T,
      MatHasDerivWithinAt U ((-Complex.I) • ((1 - U t * (U t)ᴴ) * Ω * U t)) (Icc TL T) t)
    (hU0 : U TL = Ur)
    (hZr : ∀ t ∈ Icc TL T, MatHasDerivWithinAt Zr ((-Complex.I) • (Ur ᴴ * Ω * Ur * Zr t))
      (Icc TL T) t)
    (hrank : Z TL = Ur * Zr TL) :
    ∀ t ∈ Icc TL T, Z t = U t * Zr t := by
  have hG := gram_const_of_ode hΩ (error_ode hΩ hZ hU hU0 hZr)
  intro t ht
  have h0 : Z TL - U TL * Zr TL = 0 := by rw [hU0, ← hrank, sub_self]
  have hz := eq_zero_of_gram_zero (A := Z t - U t * Zr t) (by
    rw [hG t ht]
    simp only [h0, Matrix.conjTranspose_zero, Matrix.zero_mul])
  exact sub_eq_zero.1 (by simpa using hz)

/-- Complex phase-space vector `z = S u + i Ω⁻¹ S u̇` of Prop. 3.1, with `S` playing the role of
`M^{1/2}` and `Ω⁻¹ S` the role of `B = Ω⁻¹ M^{1/2}`. -/
noncomputable def phaseVec {n : Type*} [Fintype n] [DecidableEq n] (S Ω : Matrix n n ℂ)
    (u v : ℝ → Matrix n (Fin 1) ℂ) (t : ℝ) : Matrix n (Fin 1) ℂ :=
  S * u t + Complex.I • (Ω⁻¹ * S * v t)

/-- **Prop. 3.1 (unitary complex flow), ODE part** of arXiv 2606.30469. Let `M = S²`, `Ω² = S⁻¹ K
  S⁻¹` with `Ω` invertible, and let `u` solve `M ü + K u = f` on `[a, b]` (with `v = u̇`, `acc =
  ü`). Then `z = S u + i Ω⁻¹ S u̇` satisfies `ż = -i Ω z + i Ω⁻¹ S⁻¹ f`. The paper's real data
  are the special case where all matrices and `u` are real. -/
theorem phaseVec_ode {n : Type*} [Fintype n] [DecidableEq n] {S M K Ω : Matrix n n ℂ} {a b : ℝ}
    {f : ℝ → Matrix n (Fin 1) ℂ} {u v acc : ℝ → Matrix n (Fin 1) ℂ}
    (hS : S * S = M) (hSu : IsUnit S.det) (hΩu : IsUnit Ω.det)
    (hΩ2 : Ω * Ω = S⁻¹ * K * S⁻¹)
    (hu : ∀ t ∈ Icc a b, MatHasDerivWithinAt u (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, MatHasDerivWithinAt v (acc t) (Icc a b) t)
    (hode : ∀ t ∈ Icc a b, M * acc t + K * u t = f t) :
    ∀ t ∈ Icc a b, MatHasDerivWithinAt (phaseVec S Ω u v)
      ((-Complex.I) • (Ω * phaseVec S Ω u v t) + Complex.I • (Ω⁻¹ * S⁻¹ * f t)) (Icc a b) t := by
  intro t ht
  have hKeq : K = S * (Ω * Ω) * S := by
    rw [hΩ2]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hSu]
  have hSa : S * acc t = S⁻¹ * f t - Ω * Ω * (S * u t) := by
    have h := hode t ht
    rw [← hS, hKeq] at h
    calc S * acc t = S⁻¹ * (S * S * acc t) := by
          simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hSu]
      _ = S⁻¹ * (f t - S * (Ω * Ω) * S * u t) := by
          rw [eq_sub_of_add_eq h]
      _ = S⁻¹ * f t - Ω * Ω * (S * u t) := by
          rw [Matrix.mul_sub]
          congr 1
          simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hSu]
  refine (((hu t ht).const_mul S).add
    (((hv t ht).const_mul (Ω⁻¹ * S)).smul Complex.I)).congr_deriv ?_
  simp only [phaseVec, Matrix.mul_assoc, hSa, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_nonsing_inv_cancel_left _ _ hΩu, Matrix.nonsing_inv_mul_cancel_left _ _ hΩu,
    smul_sub, smul_add]
  linear_combination (norm := module) Complex.I_sq • (S * v t)

/-- **Prop. 3.1 (unitary complex flow), unitarity.** If `Ω` is Hermitian and `f = 0` on `[a, b]`
(the wave propagation regime), then `zᴴ z` and the Frobenius norm of `z` are constant on
`[a, b]`. arXiv 2606.30469, Prop. 3.1. -/
theorem phaseVec_norm_const {n : Type*} [Fintype n] [DecidableEq n] {S M K Ω : Matrix n n ℂ}
    {a b : ℝ} {f : ℝ → Matrix n (Fin 1) ℂ} {u v acc : ℝ → Matrix n (Fin 1) ℂ}
    (hS : S * S = M) (hSu : IsUnit S.det) (hΩu : IsUnit Ω.det) (hΩH : Ωᴴ = Ω)
    (hΩ2 : Ω * Ω = S⁻¹ * K * S⁻¹)
    (hu : ∀ t ∈ Icc a b, MatHasDerivWithinAt u (v t) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, MatHasDerivWithinAt v (acc t) (Icc a b) t)
    (hode : ∀ t ∈ Icc a b, M * acc t + K * u t = f t)
    (hf : ∀ t ∈ Icc a b, f t = 0) :
    (∀ t ∈ Icc a b, (phaseVec S Ω u v t)ᴴ * phaseVec S Ω u v t
        = (phaseVec S Ω u v a)ᴴ * phaseVec S Ω u v a) ∧
    ∀ t ∈ Icc a b, frobNorm (phaseVec S Ω u v t) = frobNorm (phaseVec S Ω u v a) := by
  have hD : ∀ t ∈ Icc a b, MatHasDerivWithinAt (phaseVec S Ω u v)
      ((-Complex.I) • (Ω * phaseVec S Ω u v t)) (Icc a b) t := fun t ht =>
    (phaseVec_ode hS hSu hΩu hΩ2 hu hv hode t ht).congr_deriv (by simp [hf t ht])
  have hG := gram_const_of_ode hΩH hD
  exact ⟨hG, fun t ht => frobNorm_eq_of_gram (hG t ht)⟩

/-- Non-vacuity: the hypotheses of `phaseVec_norm_const` hold for `S = Ω = K = M = 1`, `u = v =
  0`, `f = 0`. -/
example {a b : ℝ} :
    ∀ t ∈ Icc a b, (phaseVec (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (fun _ => 0) (fun _ => 0) t)ᴴ
      * phaseVec (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (fun _ => 0) (fun _ => 0) t
      = (phaseVec (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (fun _ => 0) (fun _ => 0) a)ᴴ
      * phaseVec (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (fun _ => 0) (fun _ => 0) a :=
  (phaseVec_norm_const (S := 1) (M := 1) (K := 1) (Ω := 1) (f := fun _ => 0)
    (u := fun _ => 0) (v := fun _ => 0) (acc := fun _ => 0) (by simp) (by simp) (by simp)
    (by simp) (by simp) (fun t _ => MatHasDerivWithinAt.const 0)
    (fun t _ => MatHasDerivWithinAt.const 0) (fun t _ => by simp) (fun t _ => rfl)).1

/-- Non-vacuity of `reduced_matrix_const`: `Ω = 1` is Hermitian and the constant `U = 1`
(`1 × 1`) solves the left-basis ODE, since `1 - U Uᴴ = 0`. -/
example {a b : ℝ} :
    ∀ t ∈ Icc a b, ((fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) t)ᴴ * 1
        * (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) t
      = ((fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) a)ᴴ * 1
        * (fun _ : ℝ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) a :=
  reduced_matrix_const (Ω := 1) (by simp) fun t _ =>
    (MatHasDerivWithinAt.const 1).congr_deriv (by simp)

/-- Non-vacuity of `propagation_error_const` and `left_basis_exact`: with `Ω = 1`, the zero
solutions `Z = 0`, `U = 0`, `Zᵣ = 0`, `Ur = 0` (all `1 × 1`) satisfy all hypotheses (for any `Al`,
`Zl`, and `Z(TL) = Ur Zᵣ(TL)` for the exactness statement). -/
example {TL T : ℝ} (Al Zl : Matrix (Fin 1) (Fin 1) ℂ) :
    (∀ t ∈ Icc TL T, frobNorm ((fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t
        - (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t
          * (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t)
      = frobNorm ((fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) TL
        - (0 : Matrix (Fin 1) (Fin 1) ℂ) * ((0 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * Al * Zl))) ∧
    ∀ t ∈ Icc TL T, (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t
      = (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t
        * (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) t := by
  have h0 : ∀ (X' : Matrix (Fin 1) (Fin 1) ℂ), X' = 0 → ∀ t ∈ Icc TL T,
      MatHasDerivWithinAt (fun _ : ℝ => (0 : Matrix (Fin 1) (Fin 1) ℂ)) X' (Icc TL T) t :=
    fun X' hX' t _ => (MatHasDerivWithinAt.const 0).congr_deriv hX'.symm
  exact ⟨(propagation_error_const (Ω := 1) (Ur := 0) (by simp) (h0 _ (by simp)) (h0 _ (by simp))
      rfl (h0 _ (by simp)) (by simp)).2,
    left_basis_exact (Ω := 1) (Ur := 0) (by simp) (h0 _ (by simp)) (h0 _ (by simp)) rfl
      (h0 _ (by simp)) (by simp)⟩

/-- Relation to the core (not a paper result): for real `U` and real `X`, the complex normal
  projector `(I - Ū Ūᴴ) X̄` is the entrywise complex image of the core projector `(I - leftProj
  U) X` (`LeanDLRA.leftProj U = U Uᵀ ·`). So the complex object agrees with the real core one on
  real data. -/
theorem normal_proj_real {m k n' : Type*} [Fintype m] [DecidableEq m] [Fintype k] [Fintype n']
    (U : Matrix m k ℝ) (X : Matrix m n' ℝ) :
    (1 - (U.map Complex.ofReal) * (U.map Complex.ofReal)ᴴ) * X.map Complex.ofReal
      = ((1 - LeanDLRA.leftProj U) X).map Complex.ofReal := by
  rw [LeanDLRA.one_sub_leftProj_apply]
  ext i j
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Matrix.transpose_apply, Complex.star_def, Complex.conj_ofReal]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_zero,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]

end Calculus

end LeanDLRA.Literature.P2606_30469

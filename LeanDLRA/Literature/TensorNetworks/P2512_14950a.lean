import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2512.14950: Dynamical tensor trains for kinetics

Proved here: the exact-structure result of Sec. 4.1 for spatially homogeneous BGK, in a finite
three-index setting. A velocity tensor `f : Fin m → Fin n → Fin p → ℝ` is a 3-core tensor train;
its TT-rank bounds are the matrix ranks of the two unfoldings `unf1 f` (bond 1) and `unf2 f`
(bond 2). We prove that separable (rank-one) tensors have TT-rank `(1,1)`, that the exact
homogeneous BGK solution `(1 − e^{−ηt}) M + e^{−ηt} f₀` solves `∂ₜf = η (M − f)` with
`f(0) = f₀`, and that it has TT-rank at most `(3,3)` when `M` and `f₀` are separable, which
covers the Maxwellian and product Gaussians. A full-covariance Gaussian is not separable and is
not covered. The TT-KSL step (Sec. 3), the IMEX moment scheme (Sec. 4.4) and the second-order
Strang variant (Sec. 3.2) are not formalized: Sec. 3 would need the full TT integrator layer
(which the library lacks), Sec. 4.4 rests on an open stability claim, and Sec. 3.2 is only
observed numerically.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2512_14950

variable {m n p : ℕ}

/-- Bond-1 unfolding of a 3-index tensor: rows indexed by the first mode. -/
def unf1 (f : Fin m → Fin n → Fin p → ℝ) : Matrix (Fin m) (Fin n × Fin p) ℝ :=
  fun i jk => f i jk.1 jk.2

/-- Bond-2 unfolding of a 3-index tensor: columns indexed by the last mode. -/
def unf2 (f : Fin m → Fin n → Fin p → ℝ) : Matrix (Fin m × Fin n) (Fin p) ℝ :=
  fun ij k => f ij.1 ij.2 k

/-- TT-rank at most `(r₁, r₂)`: the two unfoldings have matrix rank at most `r₁`, `r₂`. -/
def HasTTRankLE (r₁ r₂ : ℕ) (f : Fin m → Fin n → Fin p → ℝ) : Prop :=
  (unf1 f).rank ≤ r₁ ∧ (unf2 f).rank ≤ r₂

/-- Separable (rank-one) tensor `f i j k = a i * b j * c k`. -/
def IsSeparable (f : Fin m → Fin n → Fin p → ℝ) : Prop :=
  ∃ (a : Fin m → ℝ) (b : Fin n → ℝ) (c : Fin p → ℝ), ∀ i j k, f i j k = a i * b j * c k

/-- Matrix rank is subadditive. -/
lemma rank_add_le_mat {ι κ : Type*} [Fintype κ] {A B : Matrix ι κ ℝ} :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Scaling does not increase matrix rank. -/
lemma rank_smul_le_mat {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (c : ℝ)
    (A : Matrix ι κ ℝ) : (c • A).rank ≤ A.rank := by
  have h : c • A = (c • (1 : Matrix ι ι ℝ)) * A := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h]
  exact Matrix.rank_mul_le_right _ _

lemma unf1_add (f g : Fin m → Fin n → Fin p → ℝ) : unf1 (f + g) = unf1 f + unf1 g := by
  ext i jk; rfl

lemma unf2_add (f g : Fin m → Fin n → Fin p → ℝ) : unf2 (f + g) = unf2 f + unf2 g := by
  ext ij k; rfl

lemma unf1_smul (c : ℝ) (f : Fin m → Fin n → Fin p → ℝ) : unf1 (c • f) = c • unf1 f := by
  ext i jk; rfl

lemma unf2_smul (c : ℝ) (f : Fin m → Fin n → Fin p → ℝ) : unf2 (c • f) = c • unf2 f := by
  ext ij k; rfl

/-- A separable tensor has TT-rank `(1,1)`. -/
theorem separable_hasTTRankLE {f : Fin m → Fin n → Fin p → ℝ} (hf : IsSeparable f) :
    HasTTRankLE 1 1 f := by
  obtain ⟨a, b, c, h⟩ := hf
  constructor
  · have e : unf1 f = Matrix.vecMulVec a (fun jk : Fin n × Fin p => b jk.1 * c jk.2) := by
      ext i jk
      simp only [unf1, Matrix.vecMulVec_apply, h]
      ring
    rw [e]
    exact Matrix.rank_vecMulVec_le _ _
  · have e : unf2 f = Matrix.vecMulVec (fun ij : Fin m × Fin n => a ij.1 * b ij.2) c := by
      ext ij k
      simp only [unf2, Matrix.vecMulVec_apply, h]
    rw [e]
    exact Matrix.rank_vecMulVec_le _ _

/-- The exact homogeneous BGK solution `(1 − e^{−ηt}) M + e^{−ηt} f₀` (Sec. 4.1). -/
noncomputable def bgkHomog (η : ℝ) (M f₀ : Fin m → Fin n → Fin p → ℝ) (t : ℝ) :
    Fin m → Fin n → Fin p → ℝ :=
  (1 - Real.exp (-η * t)) • M + Real.exp (-η * t) • f₀

/-- The exact homogeneous BGK solution solves `∂ₜ f = η (M − f)` with `f(0) = f₀`, for a fixed
equilibrium `M` (Sec. 4.1). -/
theorem bgkHomog_solves (η : ℝ) (M f₀ : Fin m → Fin n → Fin p → ℝ) :
    bgkHomog η M f₀ 0 = f₀ ∧
      ∀ t : ℝ, HasDerivAt (bgkHomog η M f₀) (η • (M - bgkHomog η M f₀ t)) t := by
  refine ⟨?_, fun t => ?_⟩
  · simp [bgkHomog]
  · have hs : HasDerivAt (fun t : ℝ => 1 - Real.exp (-η * t))
        (-(Real.exp (-η * t) * (-η))) t := by
      have := ((hasDerivAt_id t).const_mul (-η)).exp.const_sub 1
      simpa using this
    have he : HasDerivAt (fun t : ℝ => Real.exp (-η * t)) (Real.exp (-η * t) * (-η)) t := by
      have := ((hasDerivAt_id t).const_mul (-η)).exp
      simpa using this
    have h1 := hs.smul_const M
    have h2 := he.smul_const f₀
    have key := h1.add h2
    unfold bgkHomog
    convert key using 1
    module

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Subadditivity for two rank-one sums: a combination of two rank-`≤ 1` matrices has rank `≤ 3`. -/
lemma rank_comb_le_three {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A B : Matrix ι κ ℝ} (hA : A.rank ≤ 1) (hB : B.rank ≤ 1)
    (s e : ℝ) : (s • A + e • B).rank ≤ 3 := by
  have h1 := rank_add_le_mat (A := s • A) (B := e • B)
  have h2 := rank_smul_le_mat s A
  have h3 := rank_smul_le_mat e B
  omega

/-- Sec. 4.1: the exact homogeneous BGK solution has TT-rank at most `(3,3)` for all `t` when the
equilibrium `M` and the initial data `f₀` are separable. The proof gives rank at most `2`, by
rank subadditivity of the two rank-one terms. -/
theorem bgkHomog_hasTTRankLE (η : ℝ) {M f₀ : Fin m → Fin n → Fin p → ℝ}
    (hM : IsSeparable M) (hf₀ : IsSeparable f₀) (t : ℝ) :
    HasTTRankLE 3 3 (bgkHomog η M f₀ t) := by
  obtain ⟨hM1, hM2⟩ := separable_hasTTRankLE hM
  obtain ⟨hf1, hf2⟩ := separable_hasTTRankLE hf₀
  have e1 : unf1 (bgkHomog η M f₀ t) =
      (1 - Real.exp (-η * t)) • unf1 M + Real.exp (-η * t) • unf1 f₀ := by
    rw [bgkHomog, unf1_add, unf1_smul, unf1_smul]
  have e2 : unf2 (bgkHomog η M f₀ t) =
      (1 - Real.exp (-η * t)) • unf2 M + Real.exp (-η * t) • unf2 f₀ := by
    rw [bgkHomog, unf2_add, unf2_smul, unf2_smul]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact rank_comb_le_three hM1 hf1 _ _
  · rw [e2]
    exact rank_comb_le_three hM2 hf2 _ _

/-- The isotropic Gaussian (Maxwellian shape) on a grid, as a tensor. The normalising constant
`(2π)^{-3/2}` is omitted; it scales the tensor and does not change TT-rank. -/
noncomputable def gaussTensor (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    Fin m → Fin n → Fin p → ℝ :=
  fun i j k => Real.exp (-(x i ^ 2) / 2) * Real.exp (-(y j ^ 2) / 2) * Real.exp (-(z k ^ 2) / 2)

lemma gaussTensor_separable (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    IsSeparable (gaussTensor x y z) :=
  ⟨fun i => Real.exp (-(x i ^ 2) / 2), fun j => Real.exp (-(y j ^ 2) / 2),
    fun k => Real.exp (-(z k ^ 2) / 2), fun _ _ _ => rfl⟩

/-- The Maxwellian-shaped Gaussian tensor has TT-rank `(1,1)` (Sec. 4.1). -/
theorem gaussTensor_hasTTRankLE (x : Fin m → ℝ) (y : Fin n → ℝ) (z : Fin p → ℝ) :
    HasTTRankLE 1 1 (gaussTensor x y z) :=
  separable_hasTTRankLE (gaussTensor_separable x y z)

/-- Non-vacuity: a Gaussian Maxwellian and a Gaussian initial datum satisfy the hypotheses of
`bgkHomog_hasTTRankLE`, with TT-rank at most `(3,3)` along the whole trajectory. -/
example (η : ℝ) (t : ℝ) (x : Fin 4 → ℝ) (y : Fin 4 → ℝ) (z : Fin 4 → ℝ) :
    HasTTRankLE 3 3 (bgkHomog η (gaussTensor x y z) (gaussTensor z x y) t) :=
  bgkHomog_hasTTRankLE η (gaussTensor_separable x y z) (gaussTensor_separable z x y) t

end LeanDLRA.Literature.P2512_14950

import LeanDLRA.Classical.EckartYoung
import LeanDLRA.LinearAlgebra.LowRank.Defs

/-!
# Weyl's inequality for singular values

For a real matrix `A ∈ ℝ^{m × n}` let `σ_i(A) := (Matrix.toEuclideanLin A).singularValues i`
(Mathlib's `LinearMap.singularValues`: sorted decreasingly, zero-indexed, `0` for `i ≥ n`).
**Weyl's inequality** for singular values (Weyl 1912 for eigenvalues; Ky Fan 1951 for singular
values) states that for all `A, B ∈ ℝ^{m × n}` and all `i, j`,

  `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`.

The Frobenius analogue for the singular-value tails `τ_r(A) := (∑_{l ≥ r} σ_l(A)²)^{1/2}` reads
`τ_{i+j}(A + B) ≤ τ_i(A) + τ_j(B)`.  Standard consequences:

* **(a)** perturbation of singular values: `|σ_i(A + E) - σ_i(A)| ≤ ‖E‖₂`;
* **(b)** the `σ_r`-neighbourhood lemma: if `σ_k(X) ≥ ρ` and `‖Y - X‖₂ ≤ θ ρ`, then
  `σ_k(Y) ≥ (1 - θ) ρ` (and, for `θ < 1`, `rank Y > k`);
* **(c)** the Frobenius tail is `1`-Lipschitz: `|τ_r(A + E) - τ_r(A)| ≤ ‖E‖_F`.

## Proof strategy

Everything is reduced to the Eckart–Young–Mirsky theorem (`LeanDLRA.Classical.EckartYoung`), used
in both directions.  With the optimal truncations `A_i = A V_i V_iᵀ`, `B_j = B W_j W_jᵀ`
(`EckartYoung.truncation`) we have `‖A - A_i‖₂ = σ_i(A)`, `‖B - B_j‖₂ = σ_j(B)` (attainment),
`rank (A_i + B_j) ≤ i + j`, and the lower bound of Eckart–Young–Mirsky gives
`σ_{i+j}(A + B) ≤ ‖(A + B) - (A_i + B_j)‖₂ ≤ σ_i(A) + σ_j(B)`.  The same argument in the
Frobenius norm gives the tail version.  (a) is the case `j = 0` (`σ_0(E) = ‖E‖₂`), symmetrised;
(b) follows from (a); (c) is the `1`-Lipschitz property of `Metric.infDist`, since by
Eckart–Young–Mirsky `τ_r(A)` is the Frobenius distance from `A` to `{rank ≤ r}`.

## Main results

* `specNorm_add_le`, `specNorm_neg`: the spectral norm `LeanDLRA.Curvature.specNorm` is a norm;
* `singularValues_add_le`: **Weyl's inequality** `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`;
* `tailNorm`, `tailNorm_eq_infDist`, `tailNorm_add_le`: Frobenius tails and their Weyl
  inequality;
* `epsRank_eq_sInf_tailNorm`: the `ε`-rank `epsRank ε X` is the smallest `r` with `τ_r(X) ≤ ε`;
* `abs_singularValues_sub_le`, `abs_singularValues_add_sub_le`,
  `abs_singularValues_sub_le_frobenius`: corollary (a);
* `le_singularValues_of_specNorm_sub_le`, `lt_rank_of_specNorm_sub_le`: corollary (b);
* `abs_tailNorm_sub_le`, `abs_tailNorm_add_sub_le`: corollary (c);
* `sq_singularValues_mul_sq_norm_le`, `mul_norm_le_norm_toEuclideanLin_core`: a lower bound
  `ρ ‖w‖ ≤ ‖S w‖` for the core factor `S` of any orthonormal factorisation `X = U S Vᵀ` with
  `ρ ≤ σ_{k-1}(X)` (`k` the inner dimension).

## Connection to dynamical low-rank approximation

* `forall_mul_norm_le_core_of_specNorm_sub_le`, `koch_lubich_tangentProj_of_specNorm_sub_le`:
  the curvature condition of Koch–Lubich is stable.  If `σ_{k-1}(X₀) ≥ ρ` and the factorised
  approximation `X = U S Vᵀ` stays within `‖X - X₀‖₂ ≤ θ ρ`, `θ < 1`, then the core `S` satisfies
  the hypothesis `∀ v, (1 - θ) ρ ‖v‖ ≤ ‖S v‖` of `LeanDLRA.Curvature.koch_lubich_tangentProj`, so
  the tangent-space projector is Lipschitz at `X` with constant `2 √2 / ((1 - θ) ρ)`.
* `norm_truncation_add_sub_le_of_tail`, `lt_tailNorm_of_lt_tailNorm_sub`: the tolerance-based
  rank selection of the rank-adaptive BUG integrator (Ceruti–Kusch–Lubich, eq. (6)) is stable
  under perturbations: the rank chosen for `A` with tolerance `ϑ` meets tolerance `ϑ + ‖E‖_F`
  for `A + E`, and a rank rejected for `A` with tolerance `ϑ + ‖E‖_F` is rejected for `A + E`
  with tolerance `ϑ`.
* `tailNorm_le_norm_normal_add`: the singular-value lower bound
  `τ_{k+l}(Z) ≤ ‖(I - U Uᵀ) Z (I - V Vᵀ)‖_F` on the normal component (the modelling error `ε`)
  survives perturbations of the vector field: `τ_{k+l}(Z) ≤ ‖(I - U Uᵀ) Z' (I - V Vᵀ)‖_F +
  ‖Z - Z'‖_F`.

## Not formalised here

Mirsky's Frobenius inequality `∑_i (σ_i(A) - σ_i(B))² ≤ ‖A - B‖_F²` needs von Neumann's trace
inequality and is left for future work; corollary (c) is a weaker, tail-only consequence.

## Implementation notes

`tailNorm` is defined in `LeanDLRA/LinearAlgebra/LowRank/Defs.lean`.

## References

* H. Weyl, *Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller
  Differentialgleichungen*, Math. Ann. 71 (1912), 441–479.
* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Natl. Acad. Sci. USA 37 (1951), 760–766.
* R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis*, Cambridge Univ. Press 1991,
  Thm. 3.3.16.
* O. Koch, C. Lubich, *Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007),
  434–454.
* G. Ceruti, J. Kusch, C. Lubich, *A rank-adaptive robust integrator for dynamical low-rank
  approximation*, BIT 62 (2022), 1149–1174 (arXiv 2104.05247).
-/

open Matrix WithLp Module Finset
open scoped RealInnerProductSpace

namespace LeanDLRA.WeylSingular

open EckartYoung Curvature

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### The spectral norm is a norm -/

section SpecNorm

/-- The triangle inequality for the spectral norm. -/
theorem specNorm_add_le (A B : Matrix m n ℝ) : specNorm (A + B) ≤ specNorm A + specNorm B :=
  specNorm_le_of (add_nonneg (specNorm_nonneg A) (specNorm_nonneg B)) fun x ↦ by
    rw [map_add, LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_toEuclideanLin_le A x) (norm_toEuclideanLin_le B x))

/-- `‖-A‖₂ = ‖A‖₂`. -/
theorem specNorm_neg (A : Matrix m n ℝ) : specNorm (-A) = specNorm A := by
  simpa using specNorm_sub_comm (0 : Matrix m n ℝ) A

end SpecNorm

/-! ### Weyl's inequality -/

/-- **Weyl's inequality for singular values**: `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`. -/
theorem singularValues_add_le (A B : Matrix m n ℝ) (i j : ℕ) :
    (toEuclideanLin (A + B)).singularValues (i + j) ≤
      (toEuclideanLin A).singularValues i + (toEuclideanLin B).singularValues j := by
  have hrank : (truncation A i + truncation B j).rank ≤ i + j :=
    (rank_add_le _ _).trans (add_le_add (rank_truncation_le A i) (rank_truncation_le B j))
  calc (toEuclideanLin (A + B)).singularValues (i + j)
      ≤ specNorm (A + B - (truncation A i + truncation B j)) :=
        singularValues_le_specNorm_sub _ _ hrank
    _ = specNorm ((A - truncation A i) + (B - truncation B j)) := by congr 1; abel
    _ ≤ specNorm (A - truncation A i) + specNorm (B - truncation B j) := specNorm_add_le _ _
    _ = _ := by rw [specNorm_sub_truncation, specNorm_sub_truncation]

/-- The case `j = 0` of Weyl's inequality: `σ_i(A + E) ≤ σ_i(A) + ‖E‖₂`. -/
theorem singularValues_add_le_add_specNorm (A E : Matrix m n ℝ) (i : ℕ) :
    (toEuclideanLin (A + E)).singularValues i ≤
      (toEuclideanLin A).singularValues i + specNorm E := by
  simpa [specNorm_eq_singularValues_zero E] using singularValues_add_le A E i 0

/-- **Weyl's perturbation bound**, corollary (a): `|σ_i(A) - σ_i(B)| ≤ ‖A - B‖₂`. -/
theorem abs_singularValues_sub_le (A B : Matrix m n ℝ) (i : ℕ) :
    |(toEuclideanLin A).singularValues i - (toEuclideanLin B).singularValues i| ≤
      specNorm (A - B) := by
  have h1 := singularValues_add_le_add_specNorm B (A - B) i
  have h2 := singularValues_add_le_add_specNorm A (B - A) i
  rw [add_sub_cancel] at h1 h2
  rw [specNorm_sub_comm B A] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Corollary (a) in the form `|σ_i(A + E) - σ_i(A)| ≤ ‖E‖₂`. -/
theorem abs_singularValues_add_sub_le (A E : Matrix m n ℝ) (i : ℕ) :
    |(toEuclideanLin (A + E)).singularValues i - (toEuclideanLin A).singularValues i| ≤
      specNorm E := by
  simpa using abs_singularValues_sub_le (A + E) A i

/-- **The `σ_r`-neighbourhood lemma**, corollary (b): if `σ_k(X) ≥ ρ` and `‖Y - X‖₂ ≤ θ ρ`, then
`σ_k(Y) ≥ (1 - θ) ρ`.  (Typically `k = r - 1` for `X` of rank `r` and `0 ≤ θ < 1`.) -/
theorem le_singularValues_of_specNorm_sub_le {X Y : Matrix m n ℝ} {k : ℕ} {ρ θ : ℝ}
    (hX : ρ ≤ (toEuclideanLin X).singularValues k) (hY : specNorm (Y - X) ≤ θ * ρ) :
    (1 - θ) * ρ ≤ (toEuclideanLin Y).singularValues k := by
  have h := abs_sub_le_iff.mp (abs_singularValues_sub_le Y X k)
  linarith [h.2]

/-- Under the hypotheses of corollary (b) with `0 < ρ` and `θ < 1`, the perturbed matrix keeps
rank `> k`. -/
theorem lt_rank_of_specNorm_sub_le {X Y : Matrix m n ℝ} {k : ℕ} {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ < 1) (hX : ρ ≤ (toEuclideanLin X).singularValues k)
    (hY : specNorm (Y - X) ≤ θ * ρ) : k < Y.rank := by
  refine lt_rank_of_specNorm_sub_lt X Y ?_
  rw [specNorm_sub_comm]
  nlinarith

/-! ### Frobenius tails -/

section Frobenius

open scoped LeanDLRA.Frobenius

/- `tailNorm` is defined in `LeanDLRA/LinearAlgebra/LowRank/Defs.lean`. -/

theorem tailNorm_nonneg (A : Matrix m n ℝ) (r : ℕ) : 0 ≤ tailNorm A r :=
  Real.sqrt_nonneg _

/-- `τ_r(A) = ‖A - A V_r V_rᵀ‖_F`. -/
theorem tailNorm_eq_norm_sub_truncation (A : Matrix m n ℝ) (r : ℕ) :
    tailNorm A r = ‖A - truncation A r‖ :=
  (norm_sub_truncation A r).symm

/-- `τ_r(A) ≤ ‖A - B‖_F` whenever `rank B ≤ r`. -/
theorem tailNorm_le_norm_sub (A B : Matrix m n ℝ) {r : ℕ} (hB : B.rank ≤ r) :
    tailNorm A r ≤ ‖A - B‖ :=
  sqrt_sum_sq_singularValues_le_norm_sub A B hB

/-- `τ_r(A)` is the Frobenius distance from `A` to the matrices of rank `≤ r`. -/
theorem tailNorm_eq_infDist (A : Matrix m n ℝ) (r : ℕ) :
    tailNorm A r = Metric.infDist A {B : Matrix m n ℝ | B.rank ≤ r} :=
  (infDist_setOf_rank_le A r).symm

/-- The **`ε`-rank is the tolerance rank of the singular values**: `rank_ε(X)` is the smallest `r`
with `τ_r(X) = (∑_{l ≥ r} σ_l(X)²)^{1/2} ≤ ε`, the rank chosen by tolerance truncation of the SVD
(Eckart–Young, `tailNorm_eq_infDist`). -/
theorem epsRank_eq_sInf_tailNorm (ε : ℝ) (X : Matrix m n ℝ) :
    epsRank ε X = sInf {r | tailNorm X r ≤ ε} := by
  simp_rw [tailNorm_eq_infDist]
  rfl

/-- **Weyl's inequality for Frobenius tails**: `τ_{i+j}(A + B) ≤ τ_i(A) + τ_j(B)`. -/
theorem tailNorm_add_le (A B : Matrix m n ℝ) (i j : ℕ) :
    tailNorm (A + B) (i + j) ≤ tailNorm A i + tailNorm B j := by
  have hrank : (truncation A i + truncation B j).rank ≤ i + j :=
    (rank_add_le _ _).trans (add_le_add (rank_truncation_le A i) (rank_truncation_le B j))
  calc tailNorm (A + B) (i + j) ≤ ‖A + B - (truncation A i + truncation B j)‖ :=
        tailNorm_le_norm_sub _ _ hrank
    _ = ‖(A - truncation A i) + (B - truncation B j)‖ := by congr 1; abel
    _ ≤ ‖A - truncation A i‖ + ‖B - truncation B j‖ := norm_add_le _ _
    _ = _ := by rw [tailNorm_eq_norm_sub_truncation, tailNorm_eq_norm_sub_truncation]

/-- **The Frobenius tail is `1`-Lipschitz**, corollary (c): `|τ_r(A) - τ_r(B)| ≤ ‖A - B‖_F`. -/
theorem abs_tailNorm_sub_le (A B : Matrix m n ℝ) (r : ℕ) :
    |tailNorm A r - tailNorm B r| ≤ ‖A - B‖ := by
  rw [tailNorm_eq_infDist, tailNorm_eq_infDist, ← dist_eq_norm]
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · linarith [Metric.infDist_le_infDist_add_dist (x := A) (y := B)
      (s := {B : Matrix m n ℝ | B.rank ≤ r})]
  · linarith [Metric.infDist_le_infDist_add_dist (x := B) (y := A)
      (s := {B : Matrix m n ℝ | B.rank ≤ r}), dist_comm A B]

/-- Corollary (c) in the form `|τ_r(A + E) - τ_r(A)| ≤ ‖E‖_F`. -/
theorem abs_tailNorm_add_sub_le (A E : Matrix m n ℝ) (r : ℕ) :
    |tailNorm (A + E) r - tailNorm A r| ≤ ‖E‖ := by
  simpa using abs_tailNorm_sub_le (A + E) A r

/-- Corollary (a) in the Frobenius norm: `|σ_i(A) - σ_i(B)| ≤ ‖A - B‖_F`. -/
theorem abs_singularValues_sub_le_frobenius (A B : Matrix m n ℝ) (i : ℕ) :
    |(toEuclideanLin A).singularValues i - (toEuclideanLin B).singularValues i| ≤ ‖A - B‖ :=
  (abs_singularValues_sub_le A B i).trans (specNorm_le_frob _)

end Frobenius

/-! ### A lower bound for the core factor -/

section Core

/-- If `y` has no component along the right singular vectors `e_i`, `i ≥ K`, then
`σ_{K-1}(A)² ‖y‖² ≤ ‖A y‖²`. -/
theorem sq_singularValues_mul_sq_norm_le (A : Matrix m n ℝ) {K : ℕ} {y : EuclideanSpace ℝ n}
    (hy : ∀ i : Fin (finrank ℝ (EuclideanSpace ℝ n)), K ≤ (i : ℕ) →
      ⟪rightSingularVectors A i, y⟫ = 0) :
    (toEuclideanLin A).singularValues (K - 1) ^ 2 * ‖y‖ ^ 2 ≤ ‖toEuclideanLin A y‖ ^ 2 := by
  rw [sq_norm_toEuclideanLin_apply, ← (rightSingularVectors A).sum_sq_inner_right y,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases lt_or_ge (i : ℕ) K with hi | hi
  · exact mul_le_mul_of_nonneg_right
      (sq_singularValues_antitone (toEuclideanLin A) (by omega)) (sq_nonneg _)
  · rw [hy i hi]
    simp

/-- A matrix with orthonormal columns is an isometry. -/
theorem norm_toEuclideanLin_of_transpose_mul_eq_one {k : Type*} [Fintype k] [DecidableEq k]
    {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) (x : EuclideanSpace ℝ k) :
    ‖toEuclideanLin U x‖ = ‖x‖ := by
  have h : ‖toEuclideanLin U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [sq_norm_toEuclideanLin_eq_inner, ← LinearMap.comp_apply,
      ← toEuclideanLin_transpose_mul_self, hU, toLpLin_one, LinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Lower bound for the core factor.**  Let `X = U S Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1` and a
square core `S` of size `k`.  If `0 < ρ ≤ σ_{k-1}(X)`, then `ρ ‖w‖ ≤ ‖S w‖` for all `w`.  This
is exactly the hypothesis `hS` of `LeanDLRA.Curvature.koch_lubich_tangentProj`. -/
theorem mul_norm_le_norm_toEuclideanLin_core {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix m n ℝ} {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hX : X = U * S * Vᵀ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : ρ ≤ (toEuclideanLin X).singularValues (Fintype.card k - 1))
    (w : EuclideanSpace ℝ k) : ρ * ‖w‖ ≤ ‖toEuclideanLin S w‖ := by
  set K := Fintype.card k with hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · have : IsEmpty k := Fintype.card_eq_zero_iff.mp hK0
    rw [Subsingleton.elim w 0]
    simp
  -- rank bounds: `K ≤ rank X ≤ rank S ≤ K`
  have hrankX : K ≤ X.rank := by
    have hpos : 0 < (toEuclideanLin X).singularValues (K - 1) := hρ.trans_le hσ
    have := (LinearMap.singularValues_pos_iff_lt_finrank_range (T := toEuclideanLin X)).mp hpos
    rw [rank_eq_finrank_range]
    omega
  have hXS : X.rank ≤ S.rank :=
    hX ▸ (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hSK : S.rank ≤ K := by simpa [hK] using S.rank_le_card_width
  have hinj : Function.Injective (toEuclideanLin S) := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have := finrank_ker_add_rank S
    omega
  -- the right singular vectors `e_i`, `i ≥ K`, are annihilated by `Vᵀ`
  have hcoef : ∀ i : Fin (finrank ℝ (EuclideanSpace ℝ n)), K ≤ (i : ℕ) →
      ⟪rightSingularVectors X i, toEuclideanLin V w⟫ = 0 := by
    intro i hi
    have hσi : (toEuclideanLin X).singularValues i = 0 := by
      refine (LinearMap.singularValues_eq_zero_iff_le_finrank_range
        (T := toEuclideanLin X)).mpr ?_
      rw [← rank_eq_finrank_range]
      omega
    have hXe : toEuclideanLin X (rightSingularVectors X i) = 0 := by
      have h := sq_norm_toEuclideanLin_rightSingularVectors X i
      rw [hσi] at h
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by simpa using h))
    have hVe : toEuclideanLin Vᵀ (rightSingularVectors X i) = 0 := by
      classical
      refine hinj ?_
      have h := congrArg (toEuclideanLin Uᵀ) hXe
      rw [map_zero] at h
      rw [map_zero, ← h, hX, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← toLpLin_mul_same, ← toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU,
        Matrix.one_mul]
    rw [← LinearMap.adjoint_inner_left, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial, hVe, inner_zero_left]
  have hlow := sq_singularValues_mul_sq_norm_le X hcoef
  have hXV : toEuclideanLin X (toEuclideanLin V w) = toEuclideanLin U (toEuclideanLin S w) := by
    rw [hX, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLpLin_mul_same,
      ← toLpLin_mul_same, Matrix.mul_assoc (U * S), hV, Matrix.mul_one]
  rw [hXV, norm_toEuclideanLin_of_transpose_mul_eq_one hU,
    norm_toEuclideanLin_of_transpose_mul_eq_one hV, ← mul_pow] at hlow
  have h2 := (pow_le_pow_iff_left₀ (mul_nonneg ((toEuclideanLin X).singularValues_nonneg _)
    (norm_nonneg w)) (norm_nonneg _) two_ne_zero).mp hlow
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg w)).trans h2

end Core

/-! ### Connection to dynamical low-rank approximation -/

section DLRA

/-- **The Koch–Lubich curvature condition is stable under spectral perturbations.**  If
`σ_{k-1}(X₀) ≥ ρ > 0` and the factorised matrix `X = U S Vᵀ` (orthonormal `U`, `V`, `k × k`
core `S`) satisfies `‖X - X₀‖₂ ≤ θ ρ` with `θ < 1`, then `(1 - θ) ρ ‖v‖ ≤ ‖S v‖` for all `v`.
Along a perturbed (e.g. numerical) trajectory this supplies the hypothesis `hS` of
`LeanDLRA.Curvature.koch_lubich_tangentProj` with the radius `(1 - θ) ρ`. -/
theorem forall_mul_norm_le_core_of_specNorm_sub_le {k : Type*} [Fintype k] [DecidableEq k]
    {X₀ X : Matrix m n ℝ} {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hX : X = U * S * Vᵀ) {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ < 1) (hX₀ : ρ ≤ (toEuclideanLin X₀).singularValues (Fintype.card k - 1))
    (hXX₀ : specNorm (X - X₀) ≤ θ * ρ) (v : EuclideanSpace ℝ k) :
    (1 - θ) * ρ * ‖v‖ ≤ ‖toEuclideanLin S v‖ :=
  mul_norm_le_norm_toEuclideanLin_core hU hV hX (mul_pos (by linarith) hρ)
    (le_singularValues_of_specNorm_sub_le hX₀ hXX₀) v

section Frobenius

open scoped LeanDLRA.Frobenius

/-- **Lipschitz continuity of the tangent projector in a spectral neighbourhood.**  If
`σ_{k-1}(X₀) ≥ ρ > 0` and `X = U S Vᵀ` satisfies `‖X - X₀‖₂ ≤ θ ρ`, `θ < 1`, then for every
`Y = U' S' V'ᵀ` with orthonormal factors,
`‖P(Y) B - P(X) B‖_F ≤ 2 √2 ((1 - θ) ρ)⁻¹ ‖Y - X‖_F ‖B‖₂`
(Koch–Lubich, Lemma 4.2, with the curvature radius transported from `X₀` to `X`). -/
theorem koch_lubich_tangentProj_of_specNorm_sub_le {k : Type*} [Fintype k] [DecidableEq k]
    {X₀ : Matrix m n ℝ} {U U' : Matrix m k ℝ} {S S' : Matrix k k ℝ} {V V' : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ < 1)
    (hX₀ : ρ ≤ (toEuclideanLin X₀).singularValues (Fintype.card k - 1))
    (hXX₀ : specNorm (U * S * Vᵀ - X₀) ≤ θ * ρ) (B : Matrix m n ℝ) :
    ‖tangentProj U' V' B - tangentProj U V B‖ ≤
      2 * √2 * ((1 - θ) * ρ)⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * specNorm B :=
  koch_lubich_tangentProj (mul_pos (by linarith) hρ) hU hV hU' hV'
    (forall_mul_norm_le_core_of_specNorm_sub_le hU hV rfl hρ hθ hX₀ hXX₀) B

/-- **Stability of tolerance-based truncation** (rank-adaptive BUG, Ceruti–Kusch–Lubich
eq. (6)).  If the rank `r` meets the tolerance `ϑ` for `A`, i.e. `τ_r(A) ≤ ϑ`, then for the
perturbed matrix `A + E` the truncation to rank `r` has error at most `ϑ + ‖E‖_F`. -/
theorem norm_truncation_add_sub_le_of_tail (A E : Matrix m n ℝ) {r : ℕ} {ϑ : ℝ}
    (h : tailNorm A r ≤ ϑ) : ‖truncation (A + E) r - (A + E)‖ ≤ ϑ + ‖E‖ := by
  refine norm_sub_truncation_le_of_tail (A + E) ?_
  have := abs_sub_le_iff.mp (abs_tailNorm_add_sub_le A E r)
  change tailNorm (A + E) r ≤ ϑ + ‖E‖
  linarith [this.1]

/-- **Stability of rank rejection.**  If a rank `s` misses the tolerance `ϑ + ‖E‖_F` for `A`,
then it misses the tolerance `ϑ` for `A + E`; so the rank selected for `A + E` with tolerance
`ϑ` is at least the rank selected for `A` with tolerance `ϑ + ‖E‖_F`. -/
theorem lt_tailNorm_of_lt_tailNorm_sub (A E : Matrix m n ℝ) {s : ℕ} {ϑ : ℝ}
    (h : ϑ + ‖E‖ < tailNorm A s) : ϑ < tailNorm (A + E) s := by
  have := abs_sub_le_iff.mp (abs_tailNorm_add_sub_le A E s)
  linarith [this.2]

/-- **The singular-value lower bound on the normal component is robust.**  For arbitrary `U`
(`k` columns), `V` (`l` columns) and matrices `Z`, `Z'`,
`τ_{k+l}(Z) ≤ ‖(I - U Uᵀ) Z' (I - V Vᵀ)‖_F + ‖Z - Z'‖_F`.  In DLRA, with `Z = F(X)` and
`Z' = F(Y)` for a vector field `F` that is `L`-Lipschitz, the modelling error
`ε ≥ ‖(I - U Uᵀ) F(Y) (I - V Vᵀ)‖_F` at `Y` controls the `2r`-tail of `F` at every nearby
`X`: `τ_{2r}(F(X)) ≤ ε + L ‖X - Y‖_F`. -/
theorem tailNorm_le_norm_normal_add [DecidableEq m] {k l : Type*} [Fintype k] [Fintype l]
    (Z Z' : Matrix m n ℝ) (U : Matrix m k ℝ) (V : Matrix n l ℝ) :
    tailNorm Z (Fintype.card k + Fintype.card l) ≤
      ‖(1 - U * Uᵀ) * Z' * (1 - V * Vᵀ)‖ + ‖Z - Z'‖ := by
  have h1 : tailNorm Z' (Fintype.card k + Fintype.card l) ≤
      ‖(1 - U * Uᵀ) * Z' * (1 - V * Vᵀ)‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg _, sum_tail_le_sq_norm_normal Z' U V⟩
  have h2 := abs_sub_le_iff.mp (abs_tailNorm_sub_le Z Z' (Fintype.card k + Fintype.card l))
  linarith [h2.1]

end Frobenius

end DLRA

end LeanDLRA.WeylSingular

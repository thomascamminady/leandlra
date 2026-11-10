import Mathlib
import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Projectors
import LeanDLRA.LinearAlgebra.Frobenius.Defs
import LeanDLRA.LinearAlgebra.Projection.Defs
import LeanDLRA.FixedRank.Defs

/-!
# Curvature bounds for the manifold of fixed-rank matrices

Koch and Lubich (*Dynamical low-rank approximation*, SIAM J. Matrix Anal. Appl. 29 (2007),
Lemma 4.2; their Lemma 4.1 is the formula for `P(Y)` recalled below) bound the curvature of
the manifold `ℳ_r` of rank-`r` matrices: if `X, Y ∈ ℳ_r`, `σ_r(X) ≥ ρ > 0` and
`‖Y - X‖ ≤ ρ/8`, then for all `B`

    ‖(P(Y) - P(X)) B‖ ≤ 8 ρ⁻¹ ‖Y - X‖ ‖B‖₂,        ‖P^⊥(Y) (Y - X)‖ ≤ 4 ρ⁻¹ ‖Y - X‖²,

with `‖·‖` the Frobenius and `‖·‖₂` the spectral norm; here
`P(Y) B = U Uᵀ B + B V Vᵀ - U Uᵀ B V Vᵀ` is the orthogonal projector onto the tangent space at
`Y = U S Vᵀ` and `P^⊥(Y) B = (I - U Uᵀ) B (I - V Vᵀ)`.  These two estimates are the only
geometric input of the error analysis of the continuous DLRA problem and of the
projector-splitting integrators.  (KL07 is not in the local paper corpus.  The first estimate is
quoted in exactly this form, with `‖B‖₂`, in arXiv 2403.02834, §2; the second one, with its
constant `4`, could not be checked against a local source.  The lemma is also cited in
arXiv 1906.01369 and arXiv 2306.01485.)

**Later literature.**  Without any smallness condition, Bachmayr–Eisenmann–Kieri–Uschmajew
(arXiv 2002.12197, Lemma A.2) prove `‖(P(Y) - P(X)) B‖_F ≤ 2 σ_r(X)⁻¹ ‖Y - X‖₂ ‖B‖_F` (A.4) and
`‖P^⊥(Y)(Y - X)‖_F ≤ σ_r(X)⁻¹ ‖Y - X‖_F²` (A.5); they state that their proof is adapted from
the finite-matrix result of Wei–Cai–Chan–Leung (*Guarantees for Riemannian optimization for low
rank matrix recovery*, SIAM J. Matrix Anal. Appl. 37(3) (2016), Lemmas 4.1 & 4.2; not in the
local corpus).  So constant `1` in the normal estimate and the absence of a smallness condition
improve on KL07 only, not on this later literature.

**What is proved here.**  A purely algebraic proof via *generalized inverses* (`X G X = X`):

* normal estimate: `‖P^⊥(Y)(Y - X)‖_F ≤ ρ⁻¹ ‖Y - X‖_F²`, i.e. (A.5), and the slightly sharper
  `‖G‖₂ ‖X - Y‖₂ ‖X - Y‖_F` form (`norm_normal_sub_le_mixed`);
* tangent estimate in Koch–Lubich's norms: `‖(P(Y) - P(X)) B‖_F ≤ 2√2 ρ⁻¹ ‖Y - X‖_F ‖B‖₂`
  (`koch_lubich_tangent`: constant `2√2` instead of `8`, no smallness condition);
* tangent estimate in BEKU's norms: `‖(P(Y) - P(X)) B‖_F ≤ 2 ρ⁻¹ ‖Y - X‖₂ ‖B‖_F`
  (`koch_lubich_tangent_specNorm`, i.e. (A.4), following BEKU's proof: the spectral norm of a
  difference of two projectors is the larger of the two "sines", and for equal ranks these agree
  because `σ_min(M) = σ_min(Mᵀ)` for square `M`), with the all-Frobenius corollary
  `‖(P(Y) - P(X)) B‖_F ≤ 2 ρ⁻¹ ‖Y - X‖_F ‖B‖_F` (`koch_lubich_tangent_frob`).

The two tangent estimates are not comparable in general: (A.4) is stronger for low-rank `B`
(e.g. `‖B‖_F = ‖B‖₂`), the Koch–Lubich form for `B` of high rank (e.g. `B = I`,
`‖B‖_F = √n ‖B‖₂`) when `‖Y - X‖₂ ≈ ‖Y - X‖_F`.  Neither constant is claimed to be sharp.

*Effective ranges.*  `P(X)`, `P(Y)` and `P^⊥(Y)` are orthogonal projectors on the Frobenius space,
so `‖(P(Y) - P(X)) B‖_F ≤ ‖B‖_F` and `‖P^⊥(Y)(Y - X)‖_F ≤ ‖Y - X‖_F` hold trivially.  Hence the
all-Frobenius tangent bound says something new only for `‖Y - X‖_F < ρ/2` and the normal bound
only for `‖Y - X‖_F < ρ` (against Koch–Lubich's `ρ/8`); the spectral-`B` tangent bound can be
informative beyond `ρ/(2√2)` when `rank B > 1`.  Dropping the smallness condition is therefore
mainly a convenience (no case split), not a substantially wider region of validity.

## Ring identities (any commutative ring)

* `normal_eq_curvature`: if `X G X = X`, `Pu Y = Y` and `Y Pv = Y`, then
  `(1 - Pu) X (1 - Pv) = (1 - Pu) (X - Y) G (X - Y) (1 - Pv)`.  Since also
  `(1 - Pu) (X - Y) (1 - Pv) = (1 - Pu) X (1 - Pv)`, the normal component of `X - Y` is
  *quadratic* in `X - Y`.
* `compl_mul_colProj`: if `Pu Y = Y` then `(1 - Pu) (X G) = (1 - Pu) (X - Y) G`.
* For `X = U S Vᵀ` with `Uᵀ U = 1`, `Vᵀ V = 1` and `S` invertible, `G = V S⁻¹ Uᵀ` is the
  Moore–Penrose inverse: `X G = U Uᵀ`, `G X = V Vᵀ`, `X G X = X`, `G X G = G`.

## Norm bounds (real matrices, Frobenius norm)

We write `‖·‖` for the Frobenius norm (Mathlib's `Matrix.frobeniusNormedAddCommGroup`, activated
locally) and `specNorm` for the spectral norm (operator norm `ℓ² → ℓ²`).  The key inequalities are
`‖M B‖_F ≤ ‖M‖₂ ‖B‖_F` (`frob_mul_le`) and `‖A M‖_F ≤ ‖A‖_F ‖M‖₂` (`frob_mul_le'`).

* `norm_normal_sub_le`: `‖(1 - Pu) (X - Y) (1 - Pv)‖ ≤ ‖G‖₂ ‖X - Y‖²` for orthogonal projectors
  `Pu`, `Pv` with `Pu Y = Y`, `Y Pv = Y`.  With `G = X⁺` this is
  `‖P^⊥(Y)(Y - X)‖_F ≤ σ_r(X)⁻¹ ‖Y - X‖_F²`.  `norm_normal_sub_le_mixed` sharpens this to
  `‖G‖₂ ‖X - Y‖₂ ‖X - Y‖_F`.
* `norm_sub_sq_eq`: Pythagoras for two orthogonal projectors,
  `‖P - Q‖² = ‖(1 - Q) P‖² + ‖(1 - P) Q‖²`, and `‖P - Q‖² = 2 ‖(1 - Q) P‖²` if
  `tr P = tr Q` (equal ranks).
* `norm_colProj_sub_le`: `‖X Gx - Y Gy‖ ≤ √(‖Gx‖₂² + ‖Gy‖₂²) ‖X - Y‖` for symmetric
  column-space projectors `X Gx`, `Y Gy`; `norm_colProj_sub_le_of_trace`:
  `‖X G - P‖ ≤ √2 ‖G‖₂ ‖X - Y‖` for any orthogonal projector `P` of the same trace with `P Y = Y`.
* `tangentProjMat Pu Pv B = Pu B + B Pv - Pu B Pv`; `tangentProjMat_eq_tangentProj` identifies
  it with `LeanDLRA.tangentProj` from `Matrix/Projectors.lean` when `Pu = U Uᵀ`, `Pv = V Vᵀ`.
* `norm_tangentProjMat_sub_le`: `‖P(X) B - P(Y) B‖_F ≤ (‖ΔPu‖_F + ‖ΔPv‖_F) ‖B‖₂` (and the
  variants `norm_tangentProjMat_sub_le'` with `(‖ΔPu‖₂ + ‖ΔPv‖₂) ‖B‖_F` and
  `norm_tangentProjMat_sub_le_frob`), hence
  `‖(P(Y) - P(X)) B‖_F ≤ 2√2 σ_r(X)⁻¹ ‖Y - X‖_F ‖B‖₂` (`koch_lubich_tangent`).
* `norm_sub_mul_le_of_compl`, `specNorm_compl_mul_symm`, `norm_colProj_sub_mul_le`: the
  spectral bound `‖U' U'ᵀ - U Uᵀ‖₂ ≤ ‖G‖₂ ‖Y - X‖₂` for column projectors of equal rank
  (BEKU (A.6)).
* `koch_lubich_normal`, `koch_lubich_tangent` (and `koch_lubich_tangentProj` in terms of
  `LeanDLRA.tangentProj`): Koch–Lubich Lemma 4.2 for `X = U S Vᵀ`, `Y = U' S' V'ᵀ` with
  orthonormal factors and `σ_min(S) ≥ ρ`, with constants `1` and `2√2` and without the condition
  `‖Y - X‖ ≤ ρ/8` (`Y` need only have rank `≤ r`); `koch_lubich_tangent_specNorm` and
  `koch_lubich_tangent_frob`: the BEKU form with constant `2`; `koch_lubich_normal_svd`,
  `koch_lubich_tangent_svd` for `S = diag(σ)`, `σᵢ ≥ ρ`.
-/

open Matrix WithLp

namespace LeanDLRA

namespace Curvature

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-! ### Ring identities -/

section Algebra

variable {R : Type*} [CommRing R] [DecidableEq m] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- If `Pu Y = Y`, then the complementary projector `1 - Pu` does not see `Y`. -/
theorem compl_mul_sub {Pu : Matrix m m R} {X Y : Matrix m n R} (hu : Pu * Y = Y) :
    (1 - Pu) * (X - Y) = (1 - Pu) * X := by
  have h0 : (1 - Pu) * Y = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hu, sub_self]
  rw [Matrix.mul_sub, h0, sub_zero]

omit [Fintype m] [DecidableEq m] in
/-- If `Y Pv = Y`, then the complementary projector `1 - Pv` does not see `Y`. -/
theorem sub_mul_compl {Pv : Matrix n n R} {X Y : Matrix m n R} (hv : Y * Pv = Y) :
    (X - Y) * (1 - Pv) = X * (1 - Pv) := by
  have h0 : Y * (1 - Pv) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hv, sub_self]
  rw [Matrix.sub_mul, h0, sub_zero]

/-- The normal component of `X - Y` at `Y` equals the normal component of `X`. -/
theorem normal_sub_eq {Pu : Matrix m m R} {Pv : Matrix n n R} {X Y : Matrix m n R}
    (hu : Pu * Y = Y) (_hv : Y * Pv = Y) :
    (1 - Pu) * (X - Y) * (1 - Pv) = (1 - Pu) * X * (1 - Pv) := by
  rw [compl_mul_sub hu]

/-- **Curvature identity.** If `G` is a generalized inverse of `X` (`X G X = X`) and `Pu`, `Pv`
fix the column and row space of `Y`, then the normal component of `X` at `Y` is quadratic in
`X - Y`: `(1 - Pu) X (1 - Pv) = (1 - Pu) (X - Y) G (X - Y) (1 - Pv)`. -/
theorem normal_eq_curvature {Pu : Matrix m m R} {Pv : Matrix n n R} {X Y : Matrix m n R}
    {G : Matrix n m R} (hX : X * G * X = X) (hu : Pu * Y = Y) (hv : Y * Pv = Y) :
    (1 - Pu) * X * (1 - Pv) = (1 - Pu) * (X - Y) * G * (X - Y) * (1 - Pv) := by
  calc (1 - Pu) * X * (1 - Pv) = (1 - Pu) * (X * G * X) * (1 - Pv) := by rw [hX]
    _ = ((1 - Pu) * X) * G * (X * (1 - Pv)) := by simp only [Matrix.mul_assoc]
    _ = ((1 - Pu) * (X - Y)) * G * ((X - Y) * (1 - Pv)) := by
        rw [compl_mul_sub hu, sub_mul_compl hv]
    _ = (1 - Pu) * (X - Y) * G * (X - Y) * (1 - Pv) := by simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The column-space projector `X G` seen from the complement of the range of `Pu ⊇ col(Y)`:
`(1 - Pu) (X G) = (1 - Pu) (X - Y) G`. -/
theorem compl_mul_colProj {Pu : Matrix m m R} {X Y : Matrix m n R} (G : Matrix n m R)
    (hu : Pu * Y = Y) : (1 - Pu) * (X * G) = (1 - Pu) * (X - Y) * G := by
  rw [compl_mul_sub hu, Matrix.mul_assoc]

section Factored

variable [DecidableEq k] {U : Matrix m k R} {S : Matrix k k R} {V : Matrix n k R}

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- For `X = U S Vᵀ` with `Vᵀ V = 1` and `S` invertible, `X (V S⁻¹ Uᵀ) = U Uᵀ`. -/
theorem factor_mul_ginv (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := by
  calc U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * (S * (Vᵀ * V) * S⁻¹) * Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = U * Uᵀ := by rw [hV, Matrix.mul_one, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- For `X = U S Vᵀ` with `Uᵀ U = 1` and `S` invertible, `(V S⁻¹ Uᵀ) X = V Vᵀ`. -/
theorem ginv_mul_factor (hU : Uᵀ * U = 1) (hS : IsUnit S.det) :
    V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * Vᵀ := by
  calc V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * (S⁻¹ * (Uᵀ * U) * S) * Vᵀ := by
        simp only [Matrix.mul_assoc]
    _ = V * Vᵀ := by rw [hU, Matrix.mul_one, Matrix.nonsing_inv_mul _ hS, Matrix.mul_one]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `U Uᵀ` fixes `U S Vᵀ` when `Uᵀ U = 1`. -/
theorem colProj_mul_factor (hU : Uᵀ * U = 1) : U * Uᵀ * (U * S * Vᵀ) = U * S * Vᵀ := by
  calc U * Uᵀ * (U * S * Vᵀ) = U * (Uᵀ * U) * S * Vᵀ := by simp only [Matrix.mul_assoc]
    _ = U * S * Vᵀ := by rw [hU, Matrix.mul_one]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- `V Vᵀ` fixes `U S Vᵀ` from the right when `Vᵀ V = 1`. -/
theorem factor_mul_rowProj (hV : Vᵀ * V = 1) : U * S * Vᵀ * (V * Vᵀ) = U * S * Vᵀ := by
  calc U * S * Vᵀ * (V * Vᵀ) = U * S * (Vᵀ * V) * Vᵀ := by simp only [Matrix.mul_assoc]
    _ = U * S * Vᵀ := by rw [hV, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] in
/-- `G = V S⁻¹ Uᵀ` is a generalized inverse of `X = U S Vᵀ`: `X G X = X`. -/
theorem factor_ginv_factor (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    U * S * Vᵀ * (V * S⁻¹ * Uᵀ) * (U * S * Vᵀ) = U * S * Vᵀ := by
  rw [factor_mul_ginv hV hS, colProj_mul_factor hU]

omit [DecidableEq m] [DecidableEq n] in
/-- `G = V S⁻¹ Uᵀ` is a reflexive generalized inverse of `X = U S Vᵀ`: `G X G = G`. -/
theorem ginv_factor_ginv (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hS : IsUnit S.det) :
    V * S⁻¹ * Uᵀ * (U * S * Vᵀ) * (V * S⁻¹ * Uᵀ) = V * S⁻¹ * Uᵀ := by
  rw [ginv_mul_factor hU hS]
  calc V * Vᵀ * (V * S⁻¹ * Uᵀ) = V * (Vᵀ * V) * S⁻¹ * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = V * S⁻¹ * Uᵀ := by rw [hV, Matrix.mul_one]

end Factored

end Algebra

/-! ### The spectral norm -/

section Spectral

variable [DecidableEq m] [DecidableEq n] [DecidableEq k]

/- `specNorm` is defined in `LeanDLRA/LinearAlgebra/Frobenius/Defs.lean`. -/

section L2

open scoped Matrix.Norms.L2Operator

omit [DecidableEq m] in
lemma specNorm_eq_l2 (A : Matrix m n ℝ) : specNorm A = ‖A‖ := rfl

/-- The spectral norm is invariant under transposition. -/
lemma specNorm_transpose (A : Matrix m n ℝ) : specNorm Aᵀ = specNorm A := by
  rw [specNorm_eq_l2, specNorm_eq_l2, ← conjTranspose_eq_transpose_of_trivial,
    l2_opNorm_conjTranspose]

omit [DecidableEq m] in
/-- The spectral norm is submultiplicative. -/
lemma specNorm_mul_le (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    specNorm (A * B) ≤ specNorm A * specNorm B := by
  simpa only [specNorm_eq_l2] using l2_opNorm_mul A B

omit [DecidableEq m] in
lemma specNorm_transpose_mul_self (A : Matrix m n ℝ) :
    specNorm (Aᵀ * A) = specNorm A * specNorm A := by
  simpa only [specNorm_eq_l2, conjTranspose_eq_transpose_of_trivial] using
    l2_opNorm_conjTranspose_mul_self A

omit [DecidableEq m] in
/-- `‖A - B‖₂ = ‖B - A‖₂`. -/
lemma specNorm_sub_comm (A B : Matrix m n ℝ) : specNorm (A - B) = specNorm (B - A) := by
  rw [specNorm_eq_l2, specNorm_eq_l2, norm_sub_rev]

end L2

omit [DecidableEq m] in
lemma specNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ specNorm A := norm_nonneg _

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ ≤ specNorm A * ‖x‖ :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).le_opNorm x

omit [DecidableEq m] in
lemma specNorm_le_of {A : Matrix m n ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖Matrix.toEuclideanLin A x‖ ≤ C * ‖x‖) : specNorm A ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

lemma specNorm_one_le : specNorm (1 : Matrix n n ℝ) ≤ 1 :=
  specNorm_le_of zero_le_one fun x => by simp

omit [DecidableEq m] in
/-- A matrix with orthonormal columns has spectral norm at most one. -/
lemma specNorm_le_one_of_orthonormal {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) : specNorm U ≤ 1 := by
  have h := specNorm_transpose_mul_self U
  rw [hU] at h
  have h1 := specNorm_one_le (n := k)
  have h0 := specNorm_nonneg U
  nlinarith

/-- A matrix that is bounded below, `ρ ‖v‖ ≤ ‖S v‖` with `ρ > 0`, is invertible. -/
lemma isUnit_det_of_bounded_below {S : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) : IsUnit S.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h := hS (toLp 2 (a - b))
  have h0 : Matrix.toEuclideanLin S (toLp 2 (a - b)) = 0 := by
    rw [Matrix.toLpLin_apply]
    simp [Matrix.mulVec_sub, hab]
  rw [h0, norm_zero] at h
  have hn : ‖(toLp 2 (a - b) : EuclideanSpace ℝ k)‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h hρ) (norm_nonneg _)
  rw [norm_eq_zero] at hn
  have := congrArg ofLp hn
  simpa [sub_eq_zero] using this

/-- If `σ_min(S) ≥ ρ > 0`, i.e. `ρ ‖v‖ ≤ ‖S v‖` for all `v`, then `‖S⁻¹‖₂ ≤ ρ⁻¹`. -/
lemma specNorm_inv_le {S : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) :
    specNorm S⁻¹ ≤ ρ⁻¹ := by
  have hdet := isUnit_det_of_bounded_below hρ hS
  refine specNorm_le_of (inv_nonneg.mpr hρ.le) fun x => ?_
  have hx : Matrix.toEuclideanLin S (Matrix.toEuclideanLin S⁻¹ x) = x := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv _ hdet,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have h := hS (Matrix.toEuclideanLin S⁻¹ x)
  rw [hx] at h
  rw [inv_mul_eq_div, le_div_iff₀ hρ, mul_comm]
  exact h

omit [DecidableEq n] in
/-- For `G = V S⁻¹ Uᵀ` with orthonormal `U`, `V` and `σ_min(S) ≥ ρ > 0`: `‖G‖₂ ≤ ρ⁻¹`. -/
lemma specNorm_ginv_le {U : Matrix m k ℝ} {S : Matrix k k ℝ} {V : Matrix n k ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) :
    specNorm (V * S⁻¹ * Uᵀ) ≤ ρ⁻¹ := by
  have h1 := specNorm_mul_le (V * S⁻¹) Uᵀ
  have h2 := specNorm_mul_le V S⁻¹
  have hUt : specNorm Uᵀ ≤ 1 := by
    rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU
  have hV1 := specNorm_le_one_of_orthonormal hV
  have hSi := specNorm_inv_le hρ hS
  have := specNorm_nonneg V
  have := specNorm_nonneg S⁻¹
  have := specNorm_nonneg Uᵀ
  have := specNorm_nonneg (V * S⁻¹)
  calc specNorm (V * S⁻¹ * Uᵀ) ≤ specNorm (V * S⁻¹) * specNorm Uᵀ := h1
    _ ≤ specNorm (V * S⁻¹) * 1 := by gcongr
    _ ≤ specNorm V * specNorm S⁻¹ := by rw [mul_one]; exact h2
    _ ≤ 1 * ρ⁻¹ := by gcongr
    _ = ρ⁻¹ := one_mul _

/-- A diagonal matrix with entries `σᵢ ≥ ρ ≥ 0` is bounded below by `ρ`. -/
lemma diagonal_bounded_below {σ : k → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hσ : ∀ i, ρ ≤ σ i)
    (v : EuclideanSpace ℝ k) : ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (diagonal σ) v‖ := by
  rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, mulVec_diagonal, Real.norm_eq_abs, sq_abs,
    mul_pow]
  have : ρ ^ 2 ≤ σ i ^ 2 := pow_le_pow_left₀ hρ (hσ i) 2
  gcongr

end Spectral

/-! ### Orthogonal projectors (matrices) -/

/- `IsOrthProjMat` is defined in `LeanDLRA/LinearAlgebra/Projection/Defs.lean`. -/

namespace IsOrthProjMat

variable [DecidableEq n] {P : Matrix n n ℝ}

/-- The complementary projector `1 - P`. -/
lemma compl (hP : IsOrthProjMat P) : IsOrthProjMat (1 - P) where
  symm := by rw [transpose_sub, transpose_one, hP.symm]
  idem := by rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP.idem]; simp

/-- An orthogonal projector matrix induces an orthogonal projector on `EuclideanSpace`. -/
lemma toIsOrthProj (hP : IsOrthProjMat P) :
    IsOrthProj (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P)) where
  idem x := by
    change toEuclideanLin P (toEuclideanLin P x) = toEuclideanLin P x
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hP.idem]
  symm x y := by
    have hH : P.IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hP.symm]
    exact (isSymmetric_toEuclideanLin_iff.mpr hH) x y

/-- An orthogonal projector has spectral norm at most one. -/
lemma specNorm_le_one (hP : IsOrthProjMat P) : specNorm P ≤ 1 :=
  hP.toIsOrthProj.opNorm_le

end IsOrthProjMat

/-- `U Uᵀ` is an orthogonal projector when `U` has orthonormal columns. -/
lemma isOrthProjMat_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    IsOrthProjMat (U * Uᵀ) where
  symm := by rw [transpose_mul, transpose_transpose]
  idem := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]

/-- `X G` is an orthogonal projector if `X G X = X` and `X G` is symmetric. -/
lemma isOrthProjMat_colProj {X : Matrix m n ℝ} {G : Matrix n m ℝ} (hX : X * G * X = X)
    (hs : (X * G)ᵀ = X * G) : IsOrthProjMat (X * G) where
  symm := hs
  idem := by rw [← Matrix.mul_assoc, hX]

/-- `G X` is an orthogonal projector if `X G X = X` and `G X` is symmetric. -/
lemma isOrthProjMat_rowProj {X : Matrix m n ℝ} {G : Matrix n m ℝ} (hX : X * G * X = X)
    (hs : (G * X)ᵀ = G * X) : IsOrthProjMat (G * X) where
  symm := hs
  idem := by rw [← Matrix.mul_assoc, Matrix.mul_assoc G X G, Matrix.mul_assoc G, hX]

lemma trace_mul_transpose [DecidableEq k] {U : Matrix m k ℝ} (hU : Uᵀ * U = 1) :
    trace (U * Uᵀ) = Fintype.card k := by
  rw [trace_mul_comm, hU, trace_one]

/-! ### Frobenius-norm estimates -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

variable [DecidableEq m] [DecidableEq n] [DecidableEq k]

omit [DecidableEq m] [DecidableEq n] in
lemma frob_sq (A : Matrix m n ℝ) : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp

omit [DecidableEq m] [DecidableEq n] in
/-- The squared Frobenius norm is `tr (Aᵀ A)`. -/
lemma frob_sq_eq_trace (A : Matrix m n ℝ) : ‖A‖ ^ 2 = trace (Aᵀ * A) := by
  rw [frob_sq, Finset.sum_comm]
  simp [Matrix.trace, Matrix.mul_apply, sq]

omit [DecidableEq m] [DecidableEq n] in
/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the columns. -/
lemma frob_sq_eq_cols (A : Matrix m n ℝ) :
    ‖A‖ ^ 2 = ∑ j, ‖(toLp 2 (fun i => A i j) : EuclideanSpace ℝ m)‖ ^ 2 := by
  rw [frob_sq, Finset.sum_comm]
  simp [EuclideanSpace.norm_sq_eq]

omit [DecidableEq m] [DecidableEq k] in
/-- `‖M B‖_F ≤ ‖M‖₂ ‖B‖_F`. -/
lemma frob_mul_le (M : Matrix m n ℝ) (B : Matrix n k ℝ) : ‖M * B‖ ≤ specNorm M * ‖B‖ := by
  have hM := specNorm_nonneg M
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
    frob_sq_eq_cols, frob_sq_eq_cols, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcol : (toLp 2 (fun i => (M * B) i j) : EuclideanSpace ℝ m) =
      Matrix.toEuclideanLin M (toLp 2 (fun l => B l j)) := by
    ext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcol, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_toEuclideanLin_le _ _) 2

omit [DecidableEq m] [DecidableEq n] in
/-- `‖A M‖_F ≤ ‖A‖_F ‖M‖₂`. -/
lemma frob_mul_le' (A : Matrix m n ℝ) (M : Matrix n k ℝ) : ‖A * M‖ ≤ ‖A‖ * specNorm M := by
  classical
  calc ‖A * M‖ = ‖Mᵀ * Aᵀ‖ := by rw [← transpose_mul, frobenius_norm_transpose]
    _ ≤ specNorm Mᵀ * ‖Aᵀ‖ := frob_mul_le _ _
    _ = ‖A‖ * specNorm M := by rw [specNorm_transpose, frobenius_norm_transpose, mul_comm]

omit [DecidableEq m] in
/-- The spectral norm is bounded by the Frobenius norm. -/
lemma specNorm_le_frob (A : Matrix m n ℝ) : specNorm A ≤ ‖A‖ := by
  refine specNorm_le_of (norm_nonneg _) fun x => ?_
  have h := frobenius_norm_mul A (replicateCol Unit (ofLp x))
  rwa [← replicateCol_mulVec, frobenius_norm_replicateCol, frobenius_norm_replicateCol,
    toLp_ofLp] at h

namespace IsOrthProjMat

variable {P Q : Matrix n n ℝ}

omit [DecidableEq k] [DecidableEq n] in
/-- Multiplying by an orthogonal projector from the left does not increase the Frobenius norm. -/
lemma norm_mul_le (hP : IsOrthProjMat P) (A : Matrix n k ℝ) : ‖P * A‖ ≤ ‖A‖ := by
  classical
  exact (frob_mul_le P A).trans <| by
    simpa using mul_le_mul_of_nonneg_right hP.specNorm_le_one (norm_nonneg A)

omit [DecidableEq k] [DecidableEq n] in
/-- Multiplying by an orthogonal projector from the right does not increase the Frobenius
norm. -/
lemma norm_mul_le' (hP : IsOrthProjMat P) (A : Matrix k n ℝ) : ‖A * P‖ ≤ ‖A‖ := by
  classical
  exact (frob_mul_le' A P).trans <| by
    simpa using mul_le_mul_of_nonneg_left hP.specNorm_le_one (norm_nonneg A)

/-- `‖(1 - Q) P‖_F² = tr P - tr (P Q)` for orthogonal projectors `P`, `Q`. -/
lemma norm_compl_mul_sq (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) :
    ‖(1 - Q) * P‖ ^ 2 = trace P - trace (P * Q) := by
  rw [frob_sq_eq_trace, transpose_mul, hP.symm, hQ.compl.symm]
  have h : P * (1 - Q) * ((1 - Q) * P) = P * P - P * Q * P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q), hQ.compl.idem]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [h, trace_sub, hP.idem, trace_mul_comm (P * Q) P, ← Matrix.mul_assoc, hP.idem]

end IsOrthProjMat

/-- **Pythagoras for projector differences.** For orthogonal projectors `P`, `Q`:
`‖P - Q‖_F² = ‖(1 - Q) P‖_F² + ‖(1 - P) Q‖_F²`. -/
theorem norm_sub_sq_eq {P Q : Matrix n n ℝ} (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) :
    ‖P - Q‖ ^ 2 = ‖(1 - Q) * P‖ ^ 2 + ‖(1 - P) * Q‖ ^ 2 := by
  rw [hP.norm_compl_mul_sq hQ, hQ.norm_compl_mul_sq hP, frob_sq_eq_trace, transpose_sub,
    hP.symm, hQ.symm]
  have h : (P - Q) * (P - Q) = P * P - Q * P - (P * Q - Q * Q) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [h, hP.idem, hQ.idem, trace_sub, trace_sub, trace_sub, trace_mul_comm Q P]
  ring

/-- For orthogonal projectors of equal trace (equal rank), the two "sines" agree and
`‖P - Q‖_F² = 2 ‖(1 - Q) P‖_F²`. -/
theorem norm_sub_sq_eq_of_trace {P Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) (htr : trace P = trace Q) :
    ‖P - Q‖ ^ 2 = 2 * ‖(1 - Q) * P‖ ^ 2 := by
  rw [norm_sub_sq_eq hP hQ, hP.norm_compl_mul_sq hQ, hQ.norm_compl_mul_sq hP,
    trace_mul_comm Q P, htr]
  ring

/-- `√(a² + b²) ≤ a + b` for `a, b ≥ 0`. -/
lemma sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a ^ 2 + b ^ 2) ≤ a + b :=
  Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_nonneg ha hb]⟩

/-! #### Curvature of the fixed-rank manifold -/

omit [DecidableEq k] in
/-- **Curvature bound** (Koch–Lubich 2007, Lemma 4.2, second estimate; in the form of
Bachmayr–Eisenmann–Kieri–Uschmajew, arXiv 2002.12197, Lemma A.2 (A.5), after
Wei–Cai–Chan–Leung 2016, Lemmas 4.1 & 4.2).  Let `G` be a generalized inverse of `X`
(`X G X = X`) and let `Pu`, `Pv` be orthogonal projectors with `Pu Y = Y` and `Y Pv = Y` (e.g.
the projectors onto the column and row space of `Y`, so that
`P^⊥(Y) Z = (1 - Pu) Z (1 - Pv)`).  Then `‖(1 - Pu) (X - Y) (1 - Pv)‖_F ≤ ‖G‖₂ ‖X - Y‖_F²`.

For `G = X⁺` (Moore–Penrose) `‖G‖₂ = σ_r(X)⁻¹`, so this is `‖P^⊥(Y)(Y - X)‖ ≤ ρ⁻¹ ‖Y - X‖²`:
constant `1` instead of KL07's `4`, without KL07's assumption `‖Y - X‖ ≤ ρ / 8` (both as in
BEKU/WCCL), and neither `Y` nor `X` needs to have a particular rank.  Since the left-hand side is
trivially `≤ ‖X - Y‖_F`, the bound is informative only for `‖G‖₂ ‖X - Y‖_F < 1`. -/
theorem norm_normal_sub_le {X Y : Matrix m n ℝ} {G : Matrix n m ℝ} {Pu : Matrix m m ℝ}
    {Pv : Matrix n n ℝ} (hX : X * G * X = X) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * Y = Y) (hv : Y * Pv = Y) :
    ‖(1 - Pu) * (X - Y) * (1 - Pv)‖ ≤ specNorm G * ‖X - Y‖ ^ 2 := by
  rw [normal_sub_eq hu hv, normal_eq_curvature hX hu hv]
  have h1 : ‖(1 - Pu) * (X - Y)‖ ≤ ‖X - Y‖ := hPu.compl.norm_mul_le _
  have h2 : ‖G * ((X - Y) * (1 - Pv))‖ ≤ specNorm G * ‖X - Y‖ :=
    (frob_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hPv.compl.norm_mul_le' _) (specNorm_nonneg G))
  calc ‖(1 - Pu) * (X - Y) * G * (X - Y) * (1 - Pv)‖
      = ‖((1 - Pu) * (X - Y)) * (G * ((X - Y) * (1 - Pv)))‖ := by
        simp only [Matrix.mul_assoc]
    _ ≤ ‖(1 - Pu) * (X - Y)‖ * ‖G * ((X - Y) * (1 - Pv))‖ := frobenius_norm_mul _ _
    _ ≤ ‖X - Y‖ * (specNorm G * ‖X - Y‖) := by gcongr
    _ = specNorm G * ‖X - Y‖ ^ 2 := by ring

omit [DecidableEq k] in
/-- Frobenius version of `norm_normal_sub_le`: `‖(1 - Pu) (X - Y) (1 - Pv)‖ ≤ ‖G‖_F ‖X - Y‖²`. -/
theorem norm_normal_sub_le_frob {X Y : Matrix m n ℝ} {G : Matrix n m ℝ} {Pu : Matrix m m ℝ}
    {Pv : Matrix n n ℝ} (hX : X * G * X = X) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * Y = Y) (hv : Y * Pv = Y) :
    ‖(1 - Pu) * (X - Y) * (1 - Pv)‖ ≤ ‖G‖ * ‖X - Y‖ ^ 2 :=
  (norm_normal_sub_le hX hPu hPv hu hv).trans <| by
    gcongr; exact specNorm_le_frob G

omit [DecidableEq k] in
/-- Mixed-norm curvature bound, sharpening `norm_normal_sub_le`:
`‖(1 - Pu) (X - Y) (1 - Pv)‖_F ≤ ‖G‖₂ ‖X - Y‖₂ ‖X - Y‖_F`. -/
theorem norm_normal_sub_le_mixed {X Y : Matrix m n ℝ} {G : Matrix n m ℝ} {Pu : Matrix m m ℝ}
    {Pv : Matrix n n ℝ} (hX : X * G * X = X) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * Y = Y) (hv : Y * Pv = Y) :
    ‖(1 - Pu) * (X - Y) * (1 - Pv)‖ ≤ specNorm G * specNorm (X - Y) * ‖X - Y‖ := by
  rw [normal_sub_eq hu hv, normal_eq_curvature hX hu hv]
  have h1 : ‖(1 - Pu) * (X - Y)‖ ≤ ‖X - Y‖ := hPu.compl.norm_mul_le _
  have h2 : specNorm (G * ((X - Y) * (1 - Pv))) ≤ specNorm G * specNorm (X - Y) := by
    refine (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg G))
    calc specNorm ((X - Y) * (1 - Pv)) ≤ specNorm (X - Y) * specNorm (1 - Pv) :=
          specNorm_mul_le _ _
      _ ≤ specNorm (X - Y) * 1 :=
          mul_le_mul_of_nonneg_left hPv.compl.specNorm_le_one (specNorm_nonneg _)
      _ = specNorm (X - Y) := mul_one _
  calc ‖(1 - Pu) * (X - Y) * G * (X - Y) * (1 - Pv)‖
      = ‖((1 - Pu) * (X - Y)) * (G * ((X - Y) * (1 - Pv)))‖ := by
        simp only [Matrix.mul_assoc]
    _ ≤ ‖(1 - Pu) * (X - Y)‖ * specNorm (G * ((X - Y) * (1 - Pv))) := frob_mul_le' _ _
    _ ≤ ‖X - Y‖ * (specNorm G * specNorm (X - Y)) :=
        mul_le_mul h1 h2 (specNorm_nonneg _) (norm_nonneg _)
    _ = specNorm G * specNorm (X - Y) * ‖X - Y‖ := by ring

omit [DecidableEq k] [DecidableEq n] in
/-- One-sided projector perturbation: if the orthogonal projector `P` fixes `Y`, then
`‖(1 - P) (X G)‖_F ≤ ‖G‖₂ ‖X - Y‖_F`. -/
theorem norm_compl_mul_colProj_le {X Y : Matrix m n ℝ} (G : Matrix n m ℝ) {P : Matrix m m ℝ}
    (hP : IsOrthProjMat P) (hY : P * Y = Y) :
    ‖(1 - P) * (X * G)‖ ≤ specNorm G * ‖X - Y‖ := by
  classical
  rw [compl_mul_colProj G hY, mul_comm]
  exact (frob_mul_le' _ _).trans
    (mul_le_mul_of_nonneg_right (hP.compl.norm_mul_le _) (specNorm_nonneg G))

omit [DecidableEq k] [DecidableEq n] in
/-- **Perturbation of column-space projectors.**  If `X Gx X = X`, `Y Gy Y = Y` and the
projectors `X Gx`, `Y Gy` are symmetric (e.g. Moore–Penrose inverses), then
`‖X Gx - Y Gy‖_F ≤ √(‖Gx‖₂² + ‖Gy‖₂²) ‖X - Y‖_F` (by Pythagoras, `norm_sub_sq_eq`; see
`norm_colProj_sub_le'` for the relaxed form with `‖Gx‖₂ + ‖Gy‖₂`). -/
theorem norm_colProj_sub_le {X Y : Matrix m n ℝ} {Gx Gy : Matrix n m ℝ}
    (hX : X * Gx * X = X) (hXs : (X * Gx)ᵀ = X * Gx)
    (hY : Y * Gy * Y = Y) (hYs : (Y * Gy)ᵀ = Y * Gy) :
    ‖X * Gx - Y * Gy‖ ≤ √(specNorm Gx ^ 2 + specNorm Gy ^ 2) * ‖X - Y‖ := by
  classical
  have hPx := isOrthProjMat_colProj hX hXs
  have hPy := isOrthProjMat_colProj hY hYs
  have h1 := norm_compl_mul_colProj_le (X := X) Gx hPy hY
  have h2 := norm_compl_mul_colProj_le (X := Y) Gy hPx hX
  rw [norm_sub_rev Y X] at h2
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero,
    norm_sub_sq_eq hPx hPy, mul_pow, Real.sq_sqrt (by positivity)]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  linarith

omit [DecidableEq k] [DecidableEq n] in
/-- Relaxed form of `norm_colProj_sub_le`: `‖X Gx - Y Gy‖_F ≤ (‖Gx‖₂ + ‖Gy‖₂) ‖X - Y‖_F`. -/
theorem norm_colProj_sub_le' {X Y : Matrix m n ℝ} {Gx Gy : Matrix n m ℝ}
    (hX : X * Gx * X = X) (hXs : (X * Gx)ᵀ = X * Gx)
    (hY : Y * Gy * Y = Y) (hYs : (Y * Gy)ᵀ = Y * Gy) :
    ‖X * Gx - Y * Gy‖ ≤ (specNorm Gx + specNorm Gy) * ‖X - Y‖ :=
  (norm_colProj_sub_le hX hXs hY hYs).trans <| by
    gcongr
    exact sqrt_sq_add_sq_le (specNorm_nonneg _) (specNorm_nonneg _)

omit [DecidableEq k] [DecidableEq n] in
/-- **Perturbation of column-space projectors, equal rank** (sharp form).  If `X G X = X`,
`X G` is symmetric, and `P` is an orthogonal projector with `P Y = Y` and `tr P = tr (X G)`
(i.e. `rank P = rank X`), then `‖X G - P‖_F ≤ √2 ‖G‖₂ ‖X - Y‖_F`. -/
theorem norm_colProj_sub_le_of_trace {X Y : Matrix m n ℝ} {G : Matrix n m ℝ}
    {P : Matrix m m ℝ} (hX : X * G * X = X) (hXs : (X * G)ᵀ = X * G) (hP : IsOrthProjMat P)
    (hY : P * Y = Y) (htr : trace (X * G) = trace P) :
    ‖X * G - P‖ ≤ √2 * specNorm G * ‖X - Y‖ := by
  classical
  have hPx := isOrthProjMat_colProj hX hXs
  have h1 := norm_compl_mul_colProj_le (X := X) G hP hY
  have hg := specNorm_nonneg G
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero,
    norm_sub_sq_eq_of_trace hPx hP htr, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow] at h1'
  linarith

omit [DecidableEq k] [DecidableEq n] in
/-- Row-space version of `norm_colProj_sub_le_of_trace`: if `X G X = X`, `G X` is symmetric,
`P` is an orthogonal projector with `Y P = Y` and `tr P = tr (G X)`, then
`‖G X - P‖_F ≤ √2 ‖G‖₂ ‖X - Y‖_F`. -/
theorem norm_rowProj_sub_le_of_trace {X Y : Matrix m n ℝ} {G : Matrix n m ℝ}
    {P : Matrix n n ℝ} (hX : X * G * X = X) (hXs : (G * X)ᵀ = G * X) (hP : IsOrthProjMat P)
    (hY : Y * P = Y) (htr : trace (G * X) = trace P) :
    ‖G * X - P‖ ≤ √2 * specNorm G * ‖X - Y‖ := by
  classical
  have hT : Xᵀ * Gᵀ = G * X := by rw [← transpose_mul, hXs]
  have h := norm_colProj_sub_le_of_trace (X := Xᵀ) (G := Gᵀ) (Y := Yᵀ) (P := P)
    (by rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, hX]) (by rw [hT, hXs]) hP
    (by rw [← hP.symm, ← transpose_mul, hY]) (by rw [hT, htr])
  rwa [hT, specNorm_transpose, ← transpose_sub, frobenius_norm_transpose] at h

omit [DecidableEq k] [DecidableEq n] in
/-- Row-space version of `norm_colProj_sub_le`:
`‖Gx X - Gy Y‖_F ≤ √(‖Gx‖₂² + ‖Gy‖₂²) ‖X - Y‖_F`. -/
theorem norm_rowProj_sub_le {X Y : Matrix m n ℝ} {Gx Gy : Matrix n m ℝ}
    (hX : X * Gx * X = X) (hXs : (Gx * X)ᵀ = Gx * X)
    (hY : Y * Gy * Y = Y) (hYs : (Gy * Y)ᵀ = Gy * Y) :
    ‖Gx * X - Gy * Y‖ ≤ √(specNorm Gx ^ 2 + specNorm Gy ^ 2) * ‖X - Y‖ := by
  classical
  have hTx : Xᵀ * Gxᵀ = Gx * X := by rw [← transpose_mul, hXs]
  have hTy : Yᵀ * Gyᵀ = Gy * Y := by rw [← transpose_mul, hYs]
  have h := norm_colProj_sub_le (X := Xᵀ) (Y := Yᵀ) (Gx := Gxᵀ) (Gy := Gyᵀ)
    (by rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, hX]) (by rw [hTx, hXs])
    (by rw [← transpose_mul, ← transpose_mul, ← Matrix.mul_assoc, hY]) (by rw [hTy, hYs])
  rwa [hTx, hTy, specNorm_transpose, specNorm_transpose, ← transpose_sub,
    frobenius_norm_transpose] at h

omit [DecidableEq k] [DecidableEq n] in
/-- Relaxed form of `norm_rowProj_sub_le`: `‖Gx X - Gy Y‖_F ≤ (‖Gx‖₂ + ‖Gy‖₂) ‖X - Y‖_F`. -/
theorem norm_rowProj_sub_le' {X Y : Matrix m n ℝ} {Gx Gy : Matrix n m ℝ}
    (hX : X * Gx * X = X) (hXs : (Gx * X)ᵀ = Gx * X)
    (hY : Y * Gy * Y = Y) (hYs : (Gy * Y)ᵀ = Gy * Y) :
    ‖Gx * X - Gy * Y‖ ≤ (specNorm Gx + specNorm Gy) * ‖X - Y‖ :=
  (norm_rowProj_sub_le hX hXs hY hYs).trans <| by
    gcongr
    exact sqrt_sq_add_sq_le (specNorm_nonneg _) (specNorm_nonneg _)

/-! #### Spectral perturbation of projectors of equal rank -/

section ProjectorPerturbation

variable {l : Type*} [Fintype l]

omit [Fintype l] [DecidableEq m] [DecidableEq k] [Fintype k] in
/-- The Euclidean norm of `A x` is the Frobenius norm of `A` times the column matrix of `x`. -/
lemma norm_toEuclideanLin_eq_frob (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ = ‖A * replicateCol Unit (ofLp x)‖ := by
  rw [← replicateCol_mulVec, frobenius_norm_replicateCol]
  rfl

omit [Fintype l] [DecidableEq m] [DecidableEq k] [Fintype k] [DecidableEq n] [Fintype m] in
/-- The Euclidean norm of `x` is the Frobenius norm of its column matrix. -/
lemma norm_eq_frob_replicateCol (x : EuclideanSpace ℝ n) :
    ‖x‖ = ‖replicateCol Unit (ofLp x)‖ := by
  rw [frobenius_norm_replicateCol, toLp_ofLp]

omit [Fintype l] [DecidableEq m] [DecidableEq k] [Fintype k] in
/-- A bound `‖A B‖_F ≤ C ‖B‖_F` for all column matrices `B` bounds the spectral norm. -/
lemma specNorm_le_of_col {A : Matrix m n ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ B : Matrix n Unit ℝ, ‖A * B‖ ≤ C * ‖B‖) : specNorm A ≤ C :=
  specNorm_le_of hC fun x => by
    rw [norm_toEuclideanLin_eq_frob, norm_eq_frob_replicateCol x]
    exact h _

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- Pythagoras in the Frobenius norm: if `Xᵀ Y = 0`, then `‖X - Y‖² = ‖X‖² + ‖Y‖²`. -/
lemma frob_sq_sub_of_orth {X Y : Matrix m l ℝ} (h : Xᵀ * Y = 0) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  have h' : Yᵀ * X = 0 := by rw [← transpose_transpose X, ← transpose_mul, h, transpose_zero]
  rw [frob_sq_eq_trace, frob_sq_eq_trace, frob_sq_eq_trace, transpose_sub]
  simp only [Matrix.sub_mul, Matrix.mul_sub, h, h', trace_sub, trace_zero]
  ring

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- Pythagoras in the Frobenius norm: if `Xᵀ Y = 0`, then `‖X + Y‖² = ‖X‖² + ‖Y‖²`. -/
lemma frob_sq_add_of_orth {X Y : Matrix m l ℝ} (h : Xᵀ * Y = 0) :
    ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  rw [← sub_neg_eq_add, frob_sq_sub_of_orth (by rw [Matrix.mul_neg, h, neg_zero]), norm_neg]

omit [DecidableEq m] [DecidableEq k] in
/-- **Difference of two orthogonal projectors.**  If `‖(1 - Q) P‖₂ ≤ c` and `‖(1 - P) Q‖₂ ≤ c`,
then `‖(P - Q) B‖_F ≤ c ‖B‖_F` for every `B`.  This is the argument of arXiv 2002.12197, proof of
Lemma A.2: `(P - Q) B = (1 - Q) P B - Q (1 - P) B` is an orthogonal decomposition. -/
theorem norm_sub_mul_le_of_compl {P Q : Matrix n n ℝ} (hP : IsOrthProjMat P)
    (hQ : IsOrthProjMat Q) {c : ℝ} (hc : 0 ≤ c) (ha : specNorm ((1 - Q) * P) ≤ c)
    (hb : specNorm ((1 - P) * Q) ≤ c) (B : Matrix n l ℝ) : ‖(P - Q) * B‖ ≤ c * ‖B‖ := by
  have hsplit : (P - Q) * B = (1 - Q) * P * B - Q * (1 - P) * B := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have horth : ((1 - Q) * P * B)ᵀ * (Q * (1 - P) * B) = 0 := by
    have hQQ : (1 - Q) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQ.idem, sub_self]
    simp only [transpose_mul, hP.symm, hQ.compl.symm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 - Q) Q, hQQ, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  have hPB : (P * B)ᵀ * ((1 - P) * B) = 0 := by
    have hPP : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP.idem, sub_self]
    rw [transpose_mul, hP.symm, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP, Matrix.zero_mul,
      Matrix.mul_zero]
  have hBsplit : B = P * B + (1 - P) * B := by
    rw [Matrix.sub_mul, Matrix.one_mul]; abel
  have e1 := frob_sq_add_of_orth hPB
  rw [← hBsplit] at e1
  have h1 : ‖(1 - Q) * P * B‖ ≤ c * ‖P * B‖ := by
    have : (1 - Q) * P * B = (1 - Q) * P * (P * B) := by
      rw [← Matrix.mul_assoc ((1 - Q) * P) P B, Matrix.mul_assoc (1 - Q) P P, hP.idem]
    rw [this]
    exact (frob_mul_le _ _).trans (by gcongr)
  have h2 : ‖Q * (1 - P) * B‖ ≤ c * ‖(1 - P) * B‖ := by
    have : Q * (1 - P) * B = Q * (1 - P) * ((1 - P) * B) := by
      rw [← Matrix.mul_assoc (Q * (1 - P)) (1 - P) B, Matrix.mul_assoc Q (1 - P) (1 - P),
        hP.compl.idem]
    rw [this]
    have hb' : specNorm (Q * (1 - P)) ≤ c := by
      rw [← specNorm_transpose, transpose_mul, hQ.symm, hP.compl.symm]
      exact hb
    exact (frob_mul_le _ _).trans (by gcongr)
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, hsplit,
    frob_sq_sub_of_orth horth, mul_pow, e1]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  nlinarith

omit [DecidableEq n] in
/-- For `U`, `U'` with orthonormal columns:
`‖(1 - U' U'ᵀ) U B‖_F² = ‖B‖_F² - ‖U'ᵀ U B‖_F²`. -/
lemma frob_sq_compl_mul_orthonormal {U U' : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (hU' : U'ᵀ * U' = 1) (B : Matrix k l ℝ) :
    ‖(1 - U' * U'ᵀ) * U * B‖ ^ 2 = ‖B‖ ^ 2 - ‖U'ᵀ * U * B‖ ^ 2 := by
  have hQ := (isOrthProjMat_mul_transpose hU').compl
  rw [frob_sq_eq_trace, frob_sq_eq_trace, frob_sq_eq_trace, ← trace_sub]
  congr 1
  calc ((1 - U' * U'ᵀ) * U * B)ᵀ * ((1 - U' * U'ᵀ) * U * B)
      = Bᵀ * Uᵀ * ((1 - U' * U'ᵀ)ᵀ * (1 - U' * U'ᵀ)) * U * B := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Bᵀ * (Uᵀ * U) * B - (U'ᵀ * U * B)ᵀ * (U'ᵀ * U * B) := by
        rw [hQ.symm, hQ.idem]
        simp only [transpose_mul, transpose_transpose, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one, Matrix.mul_assoc]
    _ = Bᵀ * B - (U'ᵀ * U * B)ᵀ * (U'ᵀ * U * B) := by rw [hU, Matrix.mul_one]

omit [DecidableEq m] [DecidableEq n] [DecidableEq k] in
/-- A square matrix and its transpose have the same smallest singular value: if
`s ‖B‖_F ≤ ‖M B‖_F` for all columns `B` (`s ≥ 0`), then `s ‖B‖_F ≤ ‖Mᵀ B‖_F` for all `B`. -/
lemma bounded_below_transpose {M : Matrix k k ℝ} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ B : Matrix k Unit ℝ, s * ‖B‖ ≤ ‖M * B‖) (B : Matrix k l ℝ) :
    s * ‖B‖ ≤ ‖Mᵀ * B‖ := by
  classical
  rcases hs.eq_or_lt with rfl | hs
  · rw [zero_mul]; exact norm_nonneg _
  have hv : ∀ v : EuclideanSpace ℝ k, s * ‖v‖ ≤ ‖Matrix.toEuclideanLin M v‖ := fun v => by
    rw [norm_toEuclideanLin_eq_frob, norm_eq_frob_replicateCol v]
    exact h _
  have hdet := isUnit_det_of_bounded_below hs hv
  have hinv := specNorm_inv_le hs hv
  have hB : B = (M⁻¹)ᵀ * (Mᵀ * B) := by
    rw [← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_nonsing_inv _ hdet, transpose_one,
      Matrix.one_mul]
  have h1 : ‖B‖ ≤ s⁻¹ * ‖Mᵀ * B‖ :=
    calc ‖B‖ = ‖(M⁻¹)ᵀ * (Mᵀ * B)‖ := congrArg _ hB
      _ ≤ specNorm (M⁻¹)ᵀ * ‖Mᵀ * B‖ := frob_mul_le _ _
      _ = specNorm M⁻¹ * ‖Mᵀ * B‖ := by rw [specNorm_transpose]
      _ ≤ s⁻¹ * ‖Mᵀ * B‖ := by gcongr
  rw [inv_mul_eq_div, le_div_iff₀ hs] at h1
  linarith

omit [DecidableEq n] in
/-- **Equal-rank symmetry of the principal angles.**  For `U`, `U'` with orthonormal columns
and the *same* number `r = card k` of columns, `‖(1 - U' U'ᵀ) U‖₂ ≤ c` implies
`‖(1 - U Uᵀ) U'‖₂ ≤ c` (both norms are the sine of the largest principal angle, since
`σ_min(U'ᵀ U) = σ_min(Uᵀ U')`; cf. arXiv 2002.12197, proof of Lemma A.2). -/
theorem specNorm_compl_mul_symm {U U' : Matrix m k ℝ} (hU : Uᵀ * U = 1)
    (hU' : U'ᵀ * U' = 1) {c : ℝ} (hc : 0 ≤ c) (h : specNorm ((1 - U' * U'ᵀ) * U) ≤ c) :
    specNorm ((1 - U * Uᵀ) * U') ≤ c := by
  rcases le_or_gt 1 c with h1 | h1
  · calc _ ≤ specNorm (1 - U * Uᵀ) * specNorm U' := specNorm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (isOrthProjMat_mul_transpose hU).compl.specNorm_le_one
          (specNorm_le_one_of_orthonormal hU') (specNorm_nonneg _) zero_le_one
      _ ≤ c := by linarith
  · have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith
    have hs2 : √(1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hc2
    have hM : ∀ B : Matrix k Unit ℝ, √(1 - c ^ 2) * ‖B‖ ≤ ‖U'ᵀ * U * B‖ := by
      intro B
      have e := frob_sq_compl_mul_orthonormal hU hU' B
      have hb : ‖(1 - U' * U'ᵀ) * U * B‖ ≤ c * ‖B‖ := (frob_mul_le _ _).trans (by gcongr)
      have hb' := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow, e] at hb'
      rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow, hs2]
      nlinarith
    have hMt := bounded_below_transpose (l := Unit) (Real.sqrt_nonneg _) hM
    refine specNorm_le_of_col hc fun B => ?_
    have e := frob_sq_compl_mul_orthonormal hU' hU B
    have h2 := hMt B
    rw [transpose_mul, transpose_transpose] at h2
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, e]
    have h2' := pow_le_pow_left₀ (by positivity) h2 2
    rw [mul_pow, hs2] at h2'
    nlinarith

/-- **Spectral perturbation bound for column-space projectors** (equal rank; arXiv 2002.12197,
Lemma A.2, eq. (A.6), finite-dimensional).  Let `X G = U Uᵀ` (e.g. `X = U S Vᵀ`,
`G = V S⁻¹ Uᵀ`) and `U' U'ᵀ Y = Y`, with `U`, `U'` having orthonormal columns and the same
number of columns.  Then `‖(U' U'ᵀ - U Uᵀ) B‖_F ≤ ‖G‖₂ ‖Y - X‖₂ ‖B‖_F` for all `B` (operator
form: `specNorm_colProj_sub_le`). -/
theorem norm_colProj_sub_mul_le {X Y : Matrix m n ℝ} {G : Matrix n m ℝ} {U U' : Matrix m k ℝ}
    (hU : Uᵀ * U = 1) (hU' : U'ᵀ * U' = 1) (hXG : X * G = U * Uᵀ) (hY : U' * U'ᵀ * Y = Y)
    (B : Matrix m l ℝ) :
    ‖(U' * U'ᵀ - U * Uᵀ) * B‖ ≤ specNorm G * specNorm (Y - X) * ‖B‖ := by
  have hP := isOrthProjMat_mul_transpose hU'
  have hQ := isOrthProjMat_mul_transpose hU
  have hc : 0 ≤ specNorm G * specNorm (Y - X) :=
    mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hA : specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) ≤ specNorm G * specNorm (Y - X) := by
    rw [← hXG, compl_mul_colProj G hY, specNorm_sub_comm Y X]
    have := specNorm_nonneg G
    have := specNorm_nonneg (X - Y)
    calc specNorm ((1 - U' * U'ᵀ) * (X - Y) * G)
        ≤ specNorm ((1 - U' * U'ᵀ) * (X - Y)) * specNorm G := specNorm_mul_le _ _
      _ ≤ specNorm (1 - U' * U'ᵀ) * specNorm (X - Y) * specNorm G := by
          gcongr; exact specNorm_mul_le _ _
      _ ≤ 1 * specNorm (X - Y) * specNorm G := by
          gcongr; exact hP.compl.specNorm_le_one
      _ = specNorm G * specNorm (X - Y) := by ring
  have hA' : specNorm ((1 - U' * U'ᵀ) * U) ≤ specNorm G * specNorm (Y - X) := by
    have e : (1 - U' * U'ᵀ) * U = (1 - U' * U'ᵀ) * (U * Uᵀ) * U := by
      rw [Matrix.mul_assoc (1 - U' * U'ᵀ) (U * Uᵀ) U, Matrix.mul_assoc U, hU, Matrix.mul_one]
    rw [e]
    calc _ ≤ specNorm ((1 - U' * U'ᵀ) * (U * Uᵀ)) * specNorm U := specNorm_mul_le _ _
      _ ≤ (specNorm G * specNorm (Y - X)) * 1 :=
          mul_le_mul hA (specNorm_le_one_of_orthonormal hU) (specNorm_nonneg _) hc
      _ = _ := mul_one _
  have hB' := specNorm_compl_mul_symm hU hU' hc hA'
  have hB : specNorm ((1 - U * Uᵀ) * (U' * U'ᵀ)) ≤ specNorm G * specNorm (Y - X) := by
    rw [← Matrix.mul_assoc]
    calc _ ≤ specNorm ((1 - U * Uᵀ) * U') * specNorm U'ᵀ := specNorm_mul_le _ _
      _ ≤ (specNorm G * specNorm (Y - X)) * 1 :=
          mul_le_mul hB' (by rw [specNorm_transpose]; exact specNorm_le_one_of_orthonormal hU')
            (specNorm_nonneg _) hc
      _ = _ := mul_one _
  exact norm_sub_mul_le_of_compl hP hQ hc hB hA B

/-- Operator form of `norm_colProj_sub_mul_le`: `‖U' U'ᵀ - U Uᵀ‖₂ ≤ ‖G‖₂ ‖Y - X‖₂`. -/
theorem specNorm_colProj_sub_le {X Y : Matrix m n ℝ} {G : Matrix n m ℝ} {U U' : Matrix m k ℝ}
    (hU : Uᵀ * U = 1) (hU' : U'ᵀ * U' = 1) (hXG : X * G = U * Uᵀ) (hY : U' * U'ᵀ * Y = Y) :
    specNorm (U' * U'ᵀ - U * Uᵀ) ≤ specNorm G * specNorm (Y - X) :=
  specNorm_le_of_col (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) fun B =>
    norm_colProj_sub_mul_le hU hU' hXG hY B

end ProjectorPerturbation

/-! #### The tangent-space projector -/

/- `tangentProjMat` is defined in `LeanDLRA/FixedRank/Defs.lean`. -/

omit [DecidableEq k] [DecidableEq m] [DecidableEq n] in
/-- `tangentProjMat (U Uᵀ) (V Vᵀ)` is the tangent-space projector `LeanDLRA.tangentProj U V` of
`Matrix/Projectors.lean`. -/
theorem tangentProjMat_eq_tangentProj {k' : Type*} [Fintype k'] (U : Matrix m k ℝ)
    (V : Matrix n k' ℝ) (B : Matrix m n ℝ) :
    tangentProjMat (U * Uᵀ) (V * Vᵀ) B = tangentProj U V B := by
  rw [tangentProj_apply, tangentProjMat]
  simp only [Matrix.mul_assoc]

omit [DecidableEq k] in
/-- The normal part: `B - P(Y) B = (1 - Pu) B (1 - Pv) = P^⊥(Y) B`. -/
lemma sub_tangentProjMat (Pu : Matrix m m ℝ) (Pv : Matrix n n ℝ) (B : Matrix m n ℝ) :
    B - tangentProjMat Pu Pv B = (1 - Pu) * B * (1 - Pv) := by
  simp only [tangentProjMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  abel

omit [DecidableEq k] in
/-- Algebraic splitting of the difference of two tangent projectors:
`P B - Q B = (Pu - Qu) B (1 - Qv) + (1 - Pu) B (Pv - Qv)`. -/
lemma tangentProjMat_sub_tangentProjMat (Pu Qu : Matrix m m ℝ) (Pv Qv : Matrix n n ℝ)
    (B : Matrix m n ℝ) :
    tangentProjMat Pu Pv B - tangentProjMat Qu Qv B =
      (Pu - Qu) * B * (1 - Qv) + (1 - Pu) * B * (Pv - Qv) := by
  simp only [tangentProjMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

omit [DecidableEq k] [DecidableEq m] in
/-- **Lipschitz bound for the tangent projector in terms of the factor projectors**, with the
spectral norm of `B` (the norms of Koch–Lubich 2007, Lemma 4.2).  For orthogonal projectors `Pu`
and `Qv`: `‖P B - Q B‖_F ≤ (‖Pu - Qu‖_F + ‖Pv - Qv‖_F) ‖B‖₂`. -/
theorem norm_tangentProjMat_sub_le {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ}
    (hPu : IsOrthProjMat Pu) (hQv : IsOrthProjMat Qv) (B : Matrix m n ℝ) :
    ‖tangentProjMat Pu Pv B - tangentProjMat Qu Qv B‖ ≤ (‖Pu - Qu‖ + ‖Pv - Qv‖) * specNorm B := by
  classical
  rw [tangentProjMat_sub_tangentProjMat]
  have h1 : ‖(Pu - Qu) * B * (1 - Qv)‖ ≤ ‖Pu - Qu‖ * specNorm B :=
    (hQv.compl.norm_mul_le' _).trans (frob_mul_le' _ _)
  have h2 : ‖(1 - Pu) * B * (Pv - Qv)‖ ≤ specNorm B * ‖Pv - Qv‖ := by
    rw [Matrix.mul_assoc]
    exact (hPu.compl.norm_mul_le _).trans (frob_mul_le _ _)
  calc _ ≤ ‖(Pu - Qu) * B * (1 - Qv)‖ + ‖(1 - Pu) * B * (Pv - Qv)‖ := norm_add_le _ _
    _ ≤ ‖Pu - Qu‖ * specNorm B + specNorm B * ‖Pv - Qv‖ := add_le_add h1 h2
    _ = (‖Pu - Qu‖ + ‖Pv - Qv‖) * specNorm B := by ring

omit [DecidableEq k] in
/-- Variant of `norm_tangentProjMat_sub_le` with the spectral norms of the projector differences
and the Frobenius norm of `B` (the norms of arXiv 2002.12197, Lemma A.2 (A.4)):
`‖P B - Q B‖_F ≤ (‖Pu - Qu‖₂ + ‖Pv - Qv‖₂) ‖B‖_F`. -/
theorem norm_tangentProjMat_sub_le' {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ}
    (hPu : IsOrthProjMat Pu) (hQv : IsOrthProjMat Qv) (B : Matrix m n ℝ) :
    ‖tangentProjMat Pu Pv B - tangentProjMat Qu Qv B‖ ≤
      (specNorm (Pu - Qu) + specNorm (Pv - Qv)) * ‖B‖ := by
  classical
  rw [tangentProjMat_sub_tangentProjMat]
  have h1 : ‖(Pu - Qu) * B * (1 - Qv)‖ ≤ specNorm (Pu - Qu) * ‖B‖ :=
    (hQv.compl.norm_mul_le' _).trans (frob_mul_le _ _)
  have h2 : ‖(1 - Pu) * B * (Pv - Qv)‖ ≤ ‖B‖ * specNorm (Pv - Qv) := by
    rw [Matrix.mul_assoc]
    exact (hPu.compl.norm_mul_le _).trans (frob_mul_le' _ _)
  calc _ ≤ ‖(Pu - Qu) * B * (1 - Qv)‖ + ‖(1 - Pu) * B * (Pv - Qv)‖ := norm_add_le _ _
    _ ≤ specNorm (Pu - Qu) * ‖B‖ + ‖B‖ * specNorm (Pv - Qv) := add_le_add h1 h2
    _ = (specNorm (Pu - Qu) + specNorm (Pv - Qv)) * ‖B‖ := by ring

omit [DecidableEq k] [DecidableEq m] [DecidableEq n] in
/-- All-Frobenius corollary of `norm_tangentProjMat_sub_le`:
`‖P B - Q B‖_F ≤ (‖Pu - Qu‖_F + ‖Pv - Qv‖_F) ‖B‖_F`. -/
theorem norm_tangentProjMat_sub_le_frob {Pu Qu : Matrix m m ℝ} {Pv Qv : Matrix n n ℝ}
    (hPu : IsOrthProjMat Pu) (hQv : IsOrthProjMat Qv) (B : Matrix m n ℝ) :
    ‖tangentProjMat Pu Pv B - tangentProjMat Qu Qv B‖ ≤ (‖Pu - Qu‖ + ‖Pv - Qv‖) * ‖B‖ := by
  classical
  refine (norm_tangentProjMat_sub_le hPu hQv B).trans ?_
  have := add_nonneg (norm_nonneg (Pu - Qu)) (norm_nonneg (Pv - Qv))
  gcongr
  exact specNorm_le_frob B

omit [DecidableEq k] in
/-- **Lipschitz continuity of the tangent projector** (Koch–Lubich 2007, Lemma 4.2, first
estimate, in the paper's norms).  Let `G` be a Moore–Penrose-type inverse of `X` (`X G X = X`,
`X G` and `G X` symmetric), so that `P(X) = tangentProjMat (X G) (G X)`.  Let `Pu`, `Pv` be
orthogonal projectors with `Pu Y = Y`, `Y Pv = Y` of the same ranks as `X G`, `G X` (equal
traces).  Then `‖P(Y) B - P(X) B‖_F ≤ 2 √2 ‖G‖₂ ‖Y - X‖_F ‖B‖₂`.

Koch–Lubich have `8 ρ⁻¹ ‖Y - X‖_F ‖B‖₂` under `‖Y - X‖_F ≤ ρ/8`.  The constant `2√2` is not
sharp; it is not comparable with the constant `2` of arXiv 2002.12197, Lemma A.2 (A.4), which
uses `‖Y - X‖₂ ‖B‖_F` instead of `‖Y - X‖_F ‖B‖₂` (see the module docstring). -/
theorem norm_tangentProjMat_sub_le_of_trace {X Y : Matrix m n ℝ} {G : Matrix n m ℝ}
    {Pu : Matrix m m ℝ} {Pv : Matrix n n ℝ} (hX : X * G * X = X) (hXu : (X * G)ᵀ = X * G)
    (hXv : (G * X)ᵀ = G * X) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * Y = Y) (hv : Y * Pv = Y) (htu : trace (X * G) = trace Pu)
    (htv : trace (G * X) = trace Pv) (B : Matrix m n ℝ) :
    ‖tangentProjMat Pu Pv B - tangentProjMat (X * G) (G * X) B‖ ≤
      2 * √2 * specNorm G * ‖Y - X‖ * specNorm B := by
  classical
  have h := norm_tangentProjMat_sub_le (Qu := X * G) (Pv := Pv) hPu
    (isOrthProjMat_rowProj hX hXv) B
  have h1 := norm_colProj_sub_le_of_trace hX hXu hPu hu htu
  have h2 := norm_rowProj_sub_le_of_trace hX hXv hPv hv htv
  rw [norm_sub_rev] at h1 h2
  rw [norm_sub_rev X Y] at h1 h2
  refine h.trans ?_
  have hB := specNorm_nonneg B
  calc (‖Pu - X * G‖ + ‖Pv - G * X‖) * specNorm B
      ≤ (√2 * specNorm G * ‖Y - X‖ + √2 * specNorm G * ‖Y - X‖) * specNorm B := by gcongr
    _ = 2 * √2 * specNorm G * ‖Y - X‖ * specNorm B := by ring

omit [DecidableEq k] [DecidableEq n] in
/-- All-Frobenius corollary of `norm_tangentProjMat_sub_le_of_trace`:
`‖P(Y) B - P(X) B‖_F ≤ 2 √2 ‖G‖₂ ‖Y - X‖_F ‖B‖_F`.  This is weaker than arXiv 2002.12197,
Lemma A.2 (A.4), which gives the constant `2` (even with `‖Y - X‖₂`). -/
theorem norm_tangentProjMat_sub_le_of_trace_frob {X Y : Matrix m n ℝ} {G : Matrix n m ℝ}
    {Pu : Matrix m m ℝ} {Pv : Matrix n n ℝ} (hX : X * G * X = X) (hXu : (X * G)ᵀ = X * G)
    (hXv : (G * X)ᵀ = G * X) (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv)
    (hu : Pu * Y = Y) (hv : Y * Pv = Y) (htu : trace (X * G) = trace Pu)
    (htv : trace (G * X) = trace Pv) (B : Matrix m n ℝ) :
    ‖tangentProjMat Pu Pv B - tangentProjMat (X * G) (G * X) B‖ ≤
      2 * √2 * specNorm G * ‖Y - X‖ * ‖B‖ := by
  classical
  refine (norm_tangentProjMat_sub_le_of_trace hX hXu hXv hPu hPv hu hv htu htv B).trans ?_
  have := specNorm_nonneg G
  have := norm_nonneg (Y - X)
  gcongr
  exact specNorm_le_frob B

omit [DecidableEq k] in
/-- Lipschitz bound for the tangent projector with two generalized inverses (no rank
condition): if `X G X = X`, `Y H Y = Y` and all four projectors `X G`, `G X`, `Y H`, `H Y` are
symmetric, then `‖P(Y) B - P(X) B‖_F ≤ 2 √(‖G‖₂² + ‖H‖₂²) ‖Y - X‖_F ‖B‖₂`. -/
theorem norm_tangentProjMat_sub_le_of_ginv {X Y : Matrix m n ℝ} {G H : Matrix n m ℝ}
    (hX : X * G * X = X) (hXu : (X * G)ᵀ = X * G) (hXv : (G * X)ᵀ = G * X)
    (hY : Y * H * Y = Y) (hYu : (Y * H)ᵀ = Y * H) (hYv : (H * Y)ᵀ = H * Y)
    (B : Matrix m n ℝ) :
    ‖tangentProjMat (Y * H) (H * Y) B - tangentProjMat (X * G) (G * X) B‖ ≤
      2 * √(specNorm G ^ 2 + specNorm H ^ 2) * ‖Y - X‖ * specNorm B := by
  classical
  have h := norm_tangentProjMat_sub_le (Qu := X * G) (Pv := H * Y)
    (isOrthProjMat_colProj hY hYu) (isOrthProjMat_rowProj hX hXv) B
  have h1 := norm_colProj_sub_le hY hYu hX hXu
  have h2 := norm_rowProj_sub_le hY hYv hX hXv
  rw [add_comm (specNorm H ^ 2)] at h1 h2
  refine h.trans ?_
  have hB := specNorm_nonneg B
  calc (‖Y * H - X * G‖ + ‖H * Y - G * X‖) * specNorm B
      ≤ (√(specNorm G ^ 2 + specNorm H ^ 2) * ‖Y - X‖ +
          √(specNorm G ^ 2 + specNorm H ^ 2) * ‖Y - X‖) * specNorm B := by
        gcongr
    _ = 2 * √(specNorm G ^ 2 + specNorm H ^ 2) * ‖Y - X‖ * specNorm B := by ring

/-! #### Koch–Lubich Lemma 4.2 for factored matrices -/

/-- **Koch–Lubich 2007, Lemma 4.2 (curvature estimate)**, in the form of arXiv 2002.12197,
Lemma A.2 (A.5).  Let `X = U S Vᵀ` and `Y = U' S' V'ᵀ` with orthonormal factors
(`Uᵀ U = Vᵀ V = U'ᵀ U' = V'ᵀ V' = 1`) and let `σ_min(S) ≥ ρ > 0`, i.e. `ρ ‖v‖ ≤ ‖S v‖` (for
the SVD this is `σ_r(X) ≥ ρ`).  Then
`‖P^⊥(Y)(Y - X)‖_F = ‖(1 - U' U'ᵀ)(Y - X)(1 - V' V'ᵀ)‖_F ≤ ρ⁻¹ ‖Y - X‖_F²`.

Compared to KL07: constant `1` instead of `4`, no condition `‖Y - X‖ ≤ ρ/8`, and `S'` is
arbitrary (`Y` of rank `≤ r`).  The first two improvements are already in Wei–Cai–Chan–Leung 2016
and BEKU (arXiv 2002.12197).  As the left-hand side is trivially `≤ ‖Y - X‖_F`, the bound is
informative only for `‖Y - X‖_F < ρ`; dropping the smallness condition is a convenience. -/
theorem koch_lubich_normal {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1)
    (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) :
    ‖(1 - U' * U'ᵀ) * (U' * S' * V'ᵀ - U * S * Vᵀ) * (1 - V' * V'ᵀ)‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ ^ 2 := by
  have hdet := isUnit_det_of_bounded_below hρ hS
  have h := norm_normal_sub_le (Y := U' * S' * V'ᵀ) (G := V * S⁻¹ * Uᵀ)
    (factor_ginv_factor hU hV hdet)
    (isOrthProjMat_mul_transpose hU') (isOrthProjMat_mul_transpose hV')
    (colProj_mul_factor hU') (factor_mul_rowProj hV')
  rw [← neg_sub (U * S * Vᵀ) (U' * S' * V'ᵀ), Matrix.mul_neg, Matrix.neg_mul, norm_neg,
    norm_neg]
  exact h.trans (by gcongr; exact specNorm_ginv_le hρ hU hV hS)

omit [DecidableEq m] in
/-- **Koch–Lubich 2007, Lemma 4.2 (Lipschitz continuity of the tangent projector)**, in the
paper's norms (Frobenius norm of `Y - X`, spectral norm of `B`).  With `X = U S Vᵀ`,
`Y = U' S' V'ᵀ` as in `koch_lubich_normal` (orthonormal factors with the same number
`r = card k` of columns, `σ_min(S) ≥ ρ > 0`), for every `B`:
`‖P(Y) B - P(X) B‖_F ≤ 2 √2 ρ⁻¹ ‖Y - X‖_F ‖B‖₂`, where
`P(X) B = U Uᵀ B + B V Vᵀ - U Uᵀ B V Vᵀ`.

KL07 has the constant `8` under the condition `‖Y - X‖_F ≤ ρ/8`; here no smallness condition is
needed and `S'` is arbitrary (`Y` of rank `≤ r`).  The constant `2√2` is not claimed to be sharp.
BEKU (arXiv 2002.12197, Lemma A.2 (A.4)) prove the constant `2` with `‖Y - X‖₂ ‖B‖_F` in place of
`‖Y - X‖_F ‖B‖₂` (`koch_lubich_tangent_specNorm`), a bound that neither implies nor is implied by
this one. -/
theorem koch_lubich_tangent {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ} {S S' : Matrix k k ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1)
    (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * √2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * specNorm B := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  have hXG : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := factor_mul_ginv hV hdet
  have hGX : V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * Vᵀ := ginv_mul_factor hU hdet
  have h := norm_tangentProjMat_sub_le_of_trace (X := U * S * Vᵀ) (G := V * S⁻¹ * Uᵀ)
    (Y := U' * S' * V'ᵀ) (factor_ginv_factor hU hV hdet)
    (by rw [hXG]; exact (isOrthProjMat_mul_transpose hU).symm)
    (by rw [hGX]; exact (isOrthProjMat_mul_transpose hV).symm)
    (isOrthProjMat_mul_transpose hU') (isOrthProjMat_mul_transpose hV')
    (colProj_mul_factor hU') (factor_mul_rowProj hV')
    (by rw [hXG, trace_mul_transpose hU, trace_mul_transpose hU'])
    (by rw [hGX, trace_mul_transpose hV, trace_mul_transpose hV']) B
  rw [hXG, hGX] at h
  refine h.trans ?_
  have := specNorm_nonneg B
  have := norm_nonneg (U' * S' * V'ᵀ - U * S * Vᵀ)
  gcongr
  exact specNorm_ginv_le hρ hU hV hS

/-- `koch_lubich_normal` for a (thin) SVD `X = U diag(σ) Vᵀ` with `σᵢ ≥ ρ > 0`. -/
theorem koch_lubich_normal_svd {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ} {σ : k → ℝ}
    {S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, ρ ≤ σ i) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) :
    ‖(1 - U' * U'ᵀ) * (U' * S' * V'ᵀ - U * diagonal σ * Vᵀ) * (1 - V' * V'ᵀ)‖ ≤
      ρ⁻¹ * ‖U' * S' * V'ᵀ - U * diagonal σ * Vᵀ‖ ^ 2 :=
  koch_lubich_normal hρ hU hV hU' hV' (diagonal_bounded_below hρ.le hσ)

omit [DecidableEq m] in
/-- `koch_lubich_tangent` for a (thin) SVD `X = U diag(σ) Vᵀ` with `σᵢ ≥ ρ > 0`. -/
theorem koch_lubich_tangent_svd {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ} {σ : k → ℝ}
    {S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hσ : ∀ i, ρ ≤ σ i) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * √2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * diagonal σ * Vᵀ‖ * specNorm B := by
  classical
  exact koch_lubich_tangent hρ hU hV hU' hV' (diagonal_bounded_below hρ.le hσ) B

omit [DecidableEq m] in
/-- `koch_lubich_tangent` stated with the tangent-space projector `LeanDLRA.tangentProj` of
`Matrix/Projectors.lean`: `‖P(Y) B - P(X) B‖_F ≤ 2 √2 ρ⁻¹ ‖Y - X‖_F ‖B‖₂` for
`P(X) = tangentProj U V`, `P(Y) = tangentProj U' V'`. -/
theorem koch_lubich_tangentProj {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProj U' V' B - tangentProj U V B‖ ≤
      2 * √2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * specNorm B := by
  rw [← tangentProjMat_eq_tangentProj, ← tangentProjMat_eq_tangentProj]
  exact koch_lubich_tangent hρ hU hV hU' hV' hS B

omit [DecidableEq m] in
/-- **Lipschitz continuity of the tangent projector, spectral form** (arXiv 2002.12197,
Lemma A.2 (A.4), finite-dimensional; after Wei–Cai–Chan–Leung 2016, Lemmas 4.1 & 4.2).  With
`X = U S Vᵀ`, `Y = U' S' V'ᵀ` as in `koch_lubich_tangent` (orthonormal factors with the same
number `r` of columns, `σ_min(S) ≥ ρ > 0`, `S'` arbitrary), for every `B`:
`‖P(Y) B - P(X) B‖_F ≤ 2 ρ⁻¹ ‖Y - X‖₂ ‖B‖_F`.  No smallness condition is needed. -/
theorem koch_lubich_tangent_specNorm {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ := by
  classical
  have hdet := isUnit_det_of_bounded_below hρ hS
  have hG : specNorm (V * S⁻¹ * Uᵀ) ≤ ρ⁻¹ := specNorm_ginv_le hρ hU hV hS
  have hXG : U * S * Vᵀ * (V * S⁻¹ * Uᵀ) = U * Uᵀ := factor_mul_ginv hV hdet
  have hGX : V * S⁻¹ * Uᵀ * (U * S * Vᵀ) = V * Vᵀ := ginv_mul_factor hU hdet
  have hd := specNorm_nonneg (U' * S' * V'ᵀ - U * S * Vᵀ)
  have hcol : ∀ C : Matrix m n ℝ, ‖(U' * U'ᵀ - U * Uᵀ) * C‖ ≤
      ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖C‖ := fun C => by
    refine (norm_colProj_sub_mul_le hU hU' hXG (colProj_mul_factor (S := S') (V := V') hU')
      C).trans ?_
    have := norm_nonneg C
    gcongr
  have hY' : V' * V'ᵀ * (U' * S' * V'ᵀ)ᵀ = (U' * S' * V'ᵀ)ᵀ := by
    have h := congrArg transpose (factor_mul_rowProj (U := U') (S := S') hV')
    rwa [transpose_mul, (isOrthProjMat_mul_transpose hV').symm] at h
  have hrow : ∀ C : Matrix n m ℝ, ‖(V' * V'ᵀ - V * Vᵀ) * C‖ ≤
      ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖C‖ := fun C => by
    have h := norm_colProj_sub_mul_le (X := (U * S * Vᵀ)ᵀ) (Y := (U' * S' * V'ᵀ)ᵀ)
      (G := (V * S⁻¹ * Uᵀ)ᵀ) hV hV'
      (by rw [← transpose_mul, hGX, transpose_mul, transpose_transpose]) hY' C
    rw [specNorm_transpose, ← transpose_sub, specNorm_transpose] at h
    refine h.trans ?_
    have := norm_nonneg C
    gcongr
  rw [tangentProjMat_sub_tangentProjMat]
  have h1 : ‖(U' * U'ᵀ - U * Uᵀ) * B * (1 - V * Vᵀ)‖ ≤
      ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ :=
    ((isOrthProjMat_mul_transpose hV).compl.norm_mul_le' _).trans (hcol B)
  have h2 : ‖(1 - U' * U'ᵀ) * B * (V' * V'ᵀ - V * Vᵀ)‖ ≤
      ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ := by
    rw [Matrix.mul_assoc]
    refine ((isOrthProjMat_mul_transpose hU').compl.norm_mul_le _).trans ?_
    have hsym : (V' * V'ᵀ - V * Vᵀ)ᵀ = V' * V'ᵀ - V * Vᵀ := by
      rw [transpose_sub, (isOrthProjMat_mul_transpose hV').symm,
        (isOrthProjMat_mul_transpose hV).symm]
    calc ‖B * (V' * V'ᵀ - V * Vᵀ)‖ = ‖(V' * V'ᵀ - V * Vᵀ) * Bᵀ‖ := by
          rw [← frobenius_norm_transpose, transpose_mul, hsym]
      _ ≤ ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖Bᵀ‖ := hrow _
      _ = ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ := by
          rw [frobenius_norm_transpose]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ +
        ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ := add_le_add h1 h2
    _ = 2 * ρ⁻¹ * specNorm (U' * S' * V'ᵀ - U * S * Vᵀ) * ‖B‖ := by ring

omit [DecidableEq m] [DecidableEq n] in
/-- All-Frobenius form of the tangent estimate, with BEKU's constant `2`:
`‖P(Y) B - P(X) B‖_F ≤ 2 ρ⁻¹ ‖Y - X‖_F ‖B‖_F` (a corollary of `koch_lubich_tangent_specNorm`,
since `‖·‖₂ ≤ ‖·‖_F`).  Since `‖(P(Y) - P(X)) B‖_F ≤ ‖B‖_F` holds trivially, it is
informative only for `‖Y - X‖_F < ρ/2`. -/
theorem koch_lubich_tangent_frob {U U' : Matrix m k ℝ} {V V' : Matrix n k ℝ}
    {S S' : Matrix k k ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hU' : U'ᵀ * U' = 1) (hV' : V'ᵀ * V' = 1)
    (hS : ∀ v : EuclideanSpace ℝ k, ρ * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖) (B : Matrix m n ℝ) :
    ‖tangentProjMat (U' * U'ᵀ) (V' * V'ᵀ) B - tangentProjMat (U * Uᵀ) (V * Vᵀ) B‖ ≤
      2 * ρ⁻¹ * ‖U' * S' * V'ᵀ - U * S * Vᵀ‖ * ‖B‖ := by
  classical
  refine (koch_lubich_tangent_specNorm (S' := S') hρ hU hV hU' hV' hS B).trans ?_
  have := norm_nonneg B
  have := inv_pos.mpr hρ
  gcongr
  exact specNorm_le_frob _

/-- **Non-degenerate instance** of `koch_lubich_normal` and `koch_lubich_tangent`: rank
`r = 1 < 2 = m = n`, `X = e₁ e₁ᵀ` (`U = V = e₁`, `S = 1`, `ρ = 1`) and `Y = u uᵀ` with the
rotated unit vector `u = (3/5, 4/5)` (`U' = V' = u`, `S' = 1`).  Both theorems apply, the normal
component `P^⊥(Y)(Y - X)` is nonzero, and so is `(P(Y) - P(X)) I`. -/
example :
    let U : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]
    let U' : Matrix (Fin 2) (Fin 1) ℝ := !![3 / 5; 4 / 5]
    let S : Matrix (Fin 1) (Fin 1) ℝ := 1
    (1 - U' * U'ᵀ) * (U' * S * U'ᵀ - U * S * Uᵀ) * (1 - U' * U'ᵀ) ≠ 0 ∧
    ‖(1 - U' * U'ᵀ) * (U' * S * U'ᵀ - U * S * Uᵀ) * (1 - U' * U'ᵀ)‖ ≤
      1⁻¹ * ‖U' * S * U'ᵀ - U * S * Uᵀ‖ ^ 2 ∧
    tangentProjMat (U' * U'ᵀ) (U' * U'ᵀ) 1 - tangentProjMat (U * Uᵀ) (U * Uᵀ) 1 ≠ 0 ∧
    ‖tangentProjMat (U' * U'ᵀ) (U' * U'ᵀ) 1 - tangentProjMat (U * Uᵀ) (U * Uᵀ) 1‖ ≤
      2 * √2 * 1⁻¹ * ‖U' * S * U'ᵀ - U * S * Uᵀ‖ * specNorm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro U U' S
  have hU : Uᵀ * U = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [U, Matrix.mul_apply, Fin.sum_univ_two]
  have hU' : U'ᵀ * U' = 1 := by
    ext i j; fin_cases i; fin_cases j; simp [U', Matrix.mul_apply, Fin.sum_univ_two]; norm_num
  have hS : ∀ v : EuclideanSpace ℝ (Fin 1), (1 : ℝ) * ‖v‖ ≤ ‖Matrix.toEuclideanLin S v‖ := by
    intro v; simp [S]
  refine ⟨fun h => ?_, koch_lubich_normal one_pos hU hU hU' hU' hS, fun h => ?_,
    koch_lubich_tangent one_pos hU hU hU' hU' hS 1⟩
  · have h00 := congrFun (congrFun h 0) 0
    simp [U, U', S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
      Matrix.vecMul, dotProduct] at h00
    norm_num at h00
  · have h00 := congrFun (congrFun h 0) 0
    simp [tangentProjMat, U, U', Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct] at h00
    norm_num at h00

end Frobenius

/-! ### Projector matrices as orthogonal projectors of the Frobenius space -/

section FrobeniusProjectors

open scoped LeanDLRA.Frobenius RealInnerProductSpace

variable {P Pu : Matrix m m ℝ} {Pv : Matrix n n ℝ}

/-- Left multiplication by an orthogonal projector matrix is an orthogonal projector on the
Frobenius space of `m × l` matrices. -/
theorem IsOrthProjMat.isOrthProj_leftMulCLM {l : Type*} [Fintype l] (hP : IsOrthProjMat P) :
    IsOrthProj (Frobenius.leftMulCLM P : Matrix m l ℝ →L[ℝ] Matrix m l ℝ) where
  idem X := by
    simp only [Frobenius.leftMulCLM_apply, ← Matrix.mul_assoc, hP.idem]
  symm X Y := by
    simp only [Frobenius.leftMulCLM_apply]
    rw [Frobenius.inner_mul_left, hP.symm]

/-- Right multiplication by an orthogonal projector matrix is an orthogonal projector on the
Frobenius space of `l × n` matrices. -/
theorem IsOrthProjMat.isOrthProj_rightMulCLM {l : Type*} [Fintype l] (hP : IsOrthProjMat Pv) :
    IsOrthProj (Frobenius.rightMulCLM Pv : Matrix l n ℝ →L[ℝ] Matrix l n ℝ) where
  idem X := by
    simp only [Frobenius.rightMulCLM_apply, Matrix.mul_assoc, hP.idem]
  symm X Y := by
    simp only [Frobenius.rightMulCLM_apply]
    rw [Frobenius.inner_mul_right, hP.symm]

/-- For orthogonal projector matrices `Pu`, `Pv`, the tangent-space projector
`B ↦ tangentProjMat Pu Pv B` is an orthogonal projector of the Frobenius space
(`tangentProjMat_eq_tangent`). -/
theorem IsOrthProjMat.isOrthProj_tangent (hPu : IsOrthProjMat Pu) (hPv : IsOrthProjMat Pv) :
    IsOrthProj (tangent (Frobenius.leftMulCLM Pu) (Frobenius.rightMulCLM Pv) :
      Matrix m n ℝ →L[ℝ] Matrix m n ℝ) :=
  hPu.isOrthProj_leftMulCLM.tangent hPv.isOrthProj_rightMulCLM fun X =>
    (Matrix.mul_assoc Pu X Pv).symm

end FrobeniusProjectors

end Curvature

end LeanDLRA

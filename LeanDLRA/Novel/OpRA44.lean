import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Matrix.Curvature
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.LowRankDistance
import LeanDLRA.Stability.Energy

/-!
# Singular values of Sylvester solutions: ADI identity, explicit bounds, counterexample

Open problems OP-RA-44 (a priori ε-rank bounds from structural expansions) and OP-OT-59 (spectral
separation and singular-value decay of Sylvester solutions) of
`docs/catalogue/survey/open-problems.json`.
Everything is about actual real matrices; singular values are Mathlib's
`(toEuclideanLin X).singularValues i` (zero-based, decreasing), `specNorm` is `‖·‖₂`, `‖·‖` the
Frobenius norm, `distLR r X = dist(X, {rank ≤ r})`.

## Main results

* **ADI identity** (`sylvester_step`, `sub_adi_eq`, `rank_adi_le`): if `A X + X B = C` and the
  shifts `p_j ∉ spec A`, `-q_j ∉ spec B`, the ADI iterate `X_k` (explicit, rank `≤ k rank C`)
  satisfies `X - X_k = r_k(A) X r_k(-B)⁻¹`, `r_k(z) = ∏_{j<k} (z - q_j)/(z - p_j)`.  Hence
  (`singularValues_le`, `distLR_le`), for every `A`, `B`, with no normality assumption,
  `σ_{k rank C}(X) ≤ ‖r_k(A)‖₂ ‖X‖₂ ‖r_k(-B)⁻¹‖₂`.
* **Explicit bound for symmetric coefficients** (`SpecIn.specNorm_cayley_le`,
  `singularValues_le_cayleyRate_pow`, `distLR_le_cayleyRate_pow`, `epsRank_le_of_cayleyRate_pow`):
  for symmetric `A`, `B` with spectra in `[-b, -a]`, `0 < a ≤ b`,
  `σ_{k rank C}(X) ≤ δ^{2k} ‖X‖₂` with `δ = (√b - √a)/(√b + √a)`.  The Cayley bound
  `‖(A + √(ab))(A - √(ab))⁻¹‖₂ ≤ δ` is proved without the spectral theorem, by a Cauchy–Schwarz
  argument for the semidefinite form `⟨M x, x⟩`.
* **The Sylvester flow** `Ẋ = A X + X B + C` (`sub_eq_mexp_mul_mexp`, `rank_sub_le`,
  `singularValues_flow_le`, `specNorm_mexp_le_one`, `singularValues_flow_le_cayleyRate_pow`):
  `X(t) - Xeq = e^{tA} (X(0) - Xeq) e^{tB}` for the equilibrium `Xeq`, so
  `rank (X(t) - Xeq) = rank (X(0) - Xeq)` for all `t`, and
  `σ_{rank X(0) + 2 k rank C}(X(t)) ≤ (1 + ‖e^{tA}‖₂ ‖e^{tB}‖₂) ‖r_k(A)‖₂ ‖Xeq‖₂ ‖r_k(-B)⁻¹‖₂`;
  for symmetric negative definite coefficients `≤ 2 δ^{2k} ‖Xeq‖₂`, uniformly in `t ≥ 0`.
* **OP-OT-59 is false without normality** (`conjecture_fails`): `A = J` (nilpotent Jordan block,
  `‖J‖₂ ≤ 1`, spectrum `{0}`), `B = -K` (`K` the cyclic shift, orthogonal, spectrum on the unit
  circle), `C = -e_N e_0ᵀ` of rank one.  The solution is `X = I`: all singular values equal
  `‖X‖₂ = 1`, although the spectra of `A` and `-B` are at distance `1`, the maximum compatible
  with `‖A‖₂, ‖B‖₂ ≤ 1`.  With the normal `A' = 0` of the same spectrum the solution has rank
  `≤ 1` (`rank_le_one_of_normal_comparison`).

## Relation to prior work, and what stays open

The ADI error identity and the rank count are the mechanism of Penzl (2000) and
Beckermann–Townsend (2019); the formalisation makes the dependence on non-normality explicit as
the two norms of rational matrix functions, and the counterexample shows these norms cannot be
replaced by spectral data.  The symmetric bound `δ^{2k}` repeats the single optimal shift; Penzl's
bound with `k` distinct shifts and the Zolotarev rate `exp(-π² k / log(4 b/a))` are not
formalised (they need the spectral theorem and extremal rational functions).  Parts (i) (Dyson
series, Schrödinger) and (ii) (Riccati) of OP-RA-44 are not treated.  Nothing here assumes the
point of the theorem: every hypothesis is a condition on `A`, `B`, `C` only.
-/

open Matrix Finset

namespace LeanDLRA.Novel.OpRA44

open LeanDLRA LeanDLRA.Curvature LeanDLRA.EckartYoung

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The matrix exponential `e^A` (Mathlib's `NormedSpace.exp`, entrywise topology; defined
before the Frobenius norm is opened, as in `LeanDLRA.OpenProblems.Stiff.sylvesterFlow`). -/
noncomputable def mexp (A : Matrix m m ℝ) : Matrix m m ℝ := NormedSpace.exp A

open scoped LeanDLRA.Frobenius

/-! ### The ADI identity -/

section ADI

variable {A : Matrix m m ℝ} {B : Matrix n n ℝ} {C X : Matrix m n ℝ}

/-- One double step of the alternating-direction-implicit (ADI) iteration for `A X + X B = C`
with shifts `p` (resolvent of `A`) and `q` (resolvent of `B`), started at `0`.  The `k`-th
iterate has rank `≤ k rank C` (`rank_adi_le`). -/
noncomputable def adi (A : Matrix m m ℝ) (B : Matrix n n ℝ) (C : Matrix m n ℝ) (p q : ℕ → ℝ) :
    ℕ → Matrix m n ℝ
  | 0 => 0
  | k + 1 => ((q k - p k) • (A - p k • 1)⁻¹) * C * (B + q k • 1)⁻¹
      + (A - q k • 1) * (A - p k • 1)⁻¹ * adi A B C p q k * ((B + p k • 1) * (B + q k • 1)⁻¹)

/-- The rational matrix function `r_k(A) = ∏_{j<k} (A - q_j)(A - p_j)⁻¹`. -/
noncomputable def ratA (A : Matrix m m ℝ) (p q : ℕ → ℝ) : ℕ → Matrix m m ℝ
  | 0 => 1
  | k + 1 => (A - q k • 1) * (A - p k • 1)⁻¹ * ratA A p q k

/-- The rational matrix function `∏_{j<k} (B + p_j)(B + q_j)⁻¹ = r_k(-B)⁻¹`. -/
noncomputable def ratB (B : Matrix n n ℝ) (p q : ℕ → ℝ) : ℕ → Matrix n n ℝ
  | 0 => 1
  | k + 1 => ratB B p q k * ((B + p k • 1) * (B + q k • 1)⁻¹)

/-- Shifted copies of a matrix commute. -/
private theorem shift_comm (A : Matrix m m ℝ) (p q : ℝ) :
    (A - q • 1) * (A - p • 1) = (A - p • 1) * (A - q • 1) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_sub,
    smul_smul, mul_comm q p]
  abel

/-- The inverse of a shifted copy commutes with another shifted copy. -/
private theorem inv_shift_comm (A : Matrix m m ℝ) {p : ℝ} (q : ℝ) (hp : IsUnit (A - p • 1).det) :
    (A - p • 1)⁻¹ * (A - q • 1) = (A - q • 1) * (A - p • 1)⁻¹ := by
  calc (A - p • 1)⁻¹ * (A - q • 1)
      = (A - p • 1)⁻¹ * (A - q • 1) * ((A - p • 1) * (A - p • 1)⁻¹) := by
        rw [mul_nonsing_inv _ hp, mul_one]
    _ = (A - p • 1)⁻¹ * ((A - q • 1) * (A - p • 1)) * (A - p • 1)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (A - p • 1)⁻¹ * ((A - p • 1) * (A - q • 1)) * (A - p • 1)⁻¹ := by rw [shift_comm]
    _ = (A - q • 1) * (A - p • 1)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hp, one_mul]

/-- **The ADI fixed-point identity.**  If `A X + X B = C` and `p ∉ spec A`, `-q ∉ spec B`, then
`X = (q - p)(A - p)⁻¹ C (B + q)⁻¹ + (A - q)(A - p)⁻¹ X (B + p)(B + q)⁻¹`. -/
theorem sylvester_step (hX : A * X + X * B = C) {p q : ℝ} (hp : IsUnit (A - p • 1).det)
    (hq : IsUnit (B + q • 1).det) :
    X = ((q - p) • (A - p • 1)⁻¹) * C * (B + q • 1)⁻¹
      + (A - q • 1) * (A - p • 1)⁻¹ * X * ((B + p • 1) * (B + q • 1)⁻¹) := by
  have h1 : (A - p • 1) * X * (B + q • 1) = (q - p) • C + (A - q • 1) * X * (B + p • 1) := by
    rw [← hX]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_sub, sub_smul, smul_smul, Matrix.mul_assoc]
    module
  have h2 : (A - p • 1)⁻¹ * ((A - p • 1) * X * (B + q • 1)) * (B + q • 1)⁻¹ = X := by
    rw [Matrix.mul_assoc (A - p • 1) X, ← Matrix.mul_assoc (A - p • 1)⁻¹, nonsing_inv_mul _ hp,
      Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hq, Matrix.mul_one]
  conv_lhs => rw [← h2, h1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc]
  rw [inv_shift_comm A q hp]

/-- **The ADI error identity**: with `X_k = adi k`, `X - X_k = r_k(A) X r_k(-B)⁻¹`. -/
theorem sub_adi_eq (hX : A * X + X * B = C) {p q : ℕ → ℝ} {k : ℕ}
    (hp : ∀ j < k, IsUnit (A - p j • 1).det) (hq : ∀ j < k, IsUnit (B + q j • 1).det) :
    X - adi A B C p q k = ratA A p q k * X * ratB B p q k := by
  induction k with
  | zero => simp [adi, ratA, ratB]
  | succ k ih =>
    have ih' := ih (fun j hj => hp j (by omega)) (fun j hj => hq j (by omega))
    have hstep := sylvester_step hX (hp k (by omega)) (hq k (by omega))
    simp only [adi, ratA, ratB]
    calc X - (((q k - p k) • (A - p k • 1)⁻¹) * C * (B + q k • 1)⁻¹
          + (A - q k • 1) * (A - p k • 1)⁻¹ * adi A B C p q k * ((B + p k • 1) * (B + q k • 1)⁻¹))
        = (A - q k • 1) * (A - p k • 1)⁻¹ * (X - adi A B C p q k) *
            ((B + p k • 1) * (B + q k • 1)⁻¹) := by
          conv_lhs => rw [hstep]
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
      _ = _ := by rw [ih']; simp only [Matrix.mul_assoc]

/-- The `k`-th ADI iterate has rank at most `k · rank C`. -/
theorem rank_adi_le (A : Matrix m m ℝ) (B : Matrix n n ℝ) (C : Matrix m n ℝ) (p q : ℕ → ℝ)
    (k : ℕ) : (adi A B C p q k).rank ≤ k * C.rank := by
  induction k with
  | zero => simp [adi]
  | succ k ih =>
    simp only [adi]
    refine (rank_add_le _ _).trans ?_
    have h1 : (((q k - p k) • (A - p k • 1)⁻¹) * C * (B + q k • 1)⁻¹).rank ≤ C.rank :=
      (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    have h2 : ((A - q k • 1) * (A - p k • 1)⁻¹ * adi A B C p q k *
        ((B + p k • 1) * (B + q k • 1)⁻¹)).rank ≤ (adi A B C p q k).rank :=
      (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    calc _ ≤ C.rank + (adi A B C p q k).rank := add_le_add h1 h2
      _ ≤ C.rank + k * C.rank := by gcongr
      _ = (k + 1) * C.rank := by ring

/-- **Singular values of Sylvester solutions, general form.**  If `A X + X B = C` and the shifts
avoid the spectra, then `σ_{k rank C}(X) ≤ ‖r_k(A)‖₂ ‖X‖₂ ‖r_k(-B)⁻¹‖₂` (zero-based: this is the
`(k rank C + 1)`-st singular value).  No normality is assumed; the whole dependence on the
non-normality of `A`, `B` sits in the two spectral norms of rational matrix functions.  This is
the mechanism behind the Beckermann–Townsend bound (SIAM Rev. 2019). -/
theorem singularValues_le (hX : A * X + X * B = C) {p q : ℕ → ℝ} {k : ℕ}
    (hp : ∀ j < k, IsUnit (A - p j • 1).det) (hq : ∀ j < k, IsUnit (B + q j • 1).det) :
    (toEuclideanLin X).singularValues (k * C.rank) ≤
      specNorm (ratA A p q k) * specNorm X * specNorm (ratB B p q k) := by
  calc (toEuclideanLin X).singularValues (k * C.rank)
      ≤ specNorm (X - adi A B C p q k) :=
        singularValues_le_specNorm_sub X _ (rank_adi_le A B C p q k)
    _ = specNorm (ratA A p q k * X * ratB B p q k) := by rw [sub_adi_eq hX hp hq]
    _ ≤ specNorm (ratA A p q k * X) * specNorm (ratB B p q k) := specNorm_mul_le _ _
    _ ≤ specNorm (ratA A p q k) * specNorm X * specNorm (ratB B p q k) := by
        exact mul_le_mul_of_nonneg_right (specNorm_mul_le (ratA A p q k) X) (specNorm_nonneg _)

/-- The Frobenius form: `dist(X, M_{≤ k rank C}) ≤ ‖r_k(A)‖₂ ‖X‖_F ‖r_k(-B)⁻¹‖₂`. -/
theorem distLR_le (hX : A * X + X * B = C) {p q : ℕ → ℝ} {k : ℕ}
    (hp : ∀ j < k, IsUnit (A - p j • 1).det) (hq : ∀ j < k, IsUnit (B + q j • 1).det) :
    distLR (k * C.rank) X ≤ specNorm (ratA A p q k) * ‖X‖ * specNorm (ratB B p q k) := by
  calc distLR (k * C.rank) X ≤ ‖X - adi A B C p q k‖ :=
        distLR_le_norm_sub (rank_adi_le A B C p q k)
    _ = ‖ratA A p q k * X * ratB B p q k‖ := by rw [sub_adi_eq hX hp hq]
    _ ≤ ‖ratA A p q k * X‖ * specNorm (ratB B p q k) := frob_mul_le' _ _
    _ ≤ specNorm (ratA A p q k) * ‖X‖ * specNorm (ratB B p q k) := by
        exact mul_le_mul_of_nonneg_right (frob_mul_le (ratA A p q k) X) (specNorm_nonneg _)

end ADI

/-! ### Symmetric matrices with spectrum in an interval: an explicit Cayley bound -/

section Symmetric

variable {M A : Matrix m m ℝ}

omit [DecidableEq m] in
/-- Symmetry of the form `⟨M x, y⟩` for a symmetric matrix. -/
private theorem dot_mulVec_comm (hM : M.IsHermitian) (x y : m → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← conjTranspose_eq_transpose_of_trivial,
    hM.eq, dotProduct_comm]

omit [DecidableEq m] in
/-- Cauchy–Schwarz for the semi-inner product `(x, y) ↦ ⟨M x, y⟩` of a positive semidefinite
matrix. -/
private theorem psd_cauchy_schwarz (hM : M.PosSemidef) (x y : m → ℝ) :
    (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  have h : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (M *ᵥ y)) * (t * t) + (2 * (x ⬝ᵥ (M *ᵥ y))) * t
      + x ⬝ᵥ (M *ᵥ x) := by
    intro t
    have h0 := hM.dotProduct_mulVec_nonneg (x + t • y)
    simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, dot_mulVec_comm hM.1 y x] at h0
    nlinarith [h0]
  have hd := discrim_le_zero h
  simp only [discrim] at hd
  nlinarith [hd]

omit [DecidableEq m] in
/-- If `0 ≤ M` and `⟨M x, x⟩ ≤ c ‖x‖²` for all `x`, then `‖M x‖² ≤ c ⟨M x, x⟩`. -/
private theorem sq_norm_mulVec_le (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hMc : ∀ x, x ⬝ᵥ (M *ᵥ x) ≤ c * (x ⬝ᵥ x)) (x : m → ℝ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ x) ≤ c * (x ⬝ᵥ (M *ᵥ x)) := by
  set u := M *ᵥ x with hu
  have h1 : x ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ u := by rw [dot_mulVec_comm hM.1]
  have h2 := psd_cauchy_schwarz hM x u
  rw [h1] at h2
  have h3 := hMc u
  have h4 : 0 ≤ u ⬝ᵥ u := dotProduct_self_star_nonneg u
  have h5 : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by simpa using hM.dotProduct_mulVec_nonneg x
  rcases h4.lt_or_eq with h4 | h4
  · have : (u ⬝ᵥ u) * (u ⬝ᵥ u) ≤ (u ⬝ᵥ u) * (c * (x ⬝ᵥ (M *ᵥ x))) := by nlinarith
    exact le_of_mul_le_mul_left this h4
  · rw [← h4]; positivity

/-- The hypothesis `-b ≤ A ≤ -a` in the sense of quadratic forms: `-(A + a I)` and `A + b I` are
positive semidefinite (`A` symmetric). -/
def SpecIn (A : Matrix m m ℝ) (a b : ℝ) : Prop :=
  (-(A + a • (1 : Matrix m m ℝ))).PosSemidef ∧ (A + b • (1 : Matrix m m ℝ)).PosSemidef

theorem SpecIn.isHermitian (h : SpecIn A a b) : A.IsHermitian := by
  have h1 := h.1.1
  simp only [IsHermitian, conjTranspose_neg, conjTranspose_add, conjTranspose_smul,
    conjTranspose_one, star_trivial, neg_inj, add_left_inj] at h1
  exact h1

theorem SpecIn.upper (h : SpecIn A a b) (x : m → ℝ) : x ⬝ᵥ (A *ᵥ x) ≤ -a * (x ⬝ᵥ x) := by
  have := h.1.dotProduct_mulVec_nonneg x
  rw [star_trivial, neg_mulVec, dotProduct_neg, add_mulVec, dotProduct_add, smul_mulVec,
    one_mulVec, dotProduct_smul] at this
  simp only [smul_eq_mul] at this
  linarith

theorem SpecIn.lower (h : SpecIn A a b) (x : m → ℝ) : -b * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have := h.2.dotProduct_mulVec_nonneg x
  rw [star_trivial, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul] at this
  simp only [smul_eq_mul] at this
  linarith

/-- The key quadratic inequality: for `-b ≤ A ≤ -a`,
`‖A x‖² + a b ‖x‖² ≤ (a + b) ⟨-A x, x⟩`. -/
theorem SpecIn.sq_norm_mulVec_add_le (h : SpecIn A a b) (hab : a ≤ b) (x : m → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) + a * b * (x ⬝ᵥ x) ≤ (a + b) * (-(x ⬝ᵥ (A *ᵥ x))) := by
  set M := -(A + a • (1 : Matrix m m ℝ)) with hM
  have hMc : ∀ y, y ⬝ᵥ (M *ᵥ y) ≤ (b - a) * (y ⬝ᵥ y) := by
    intro y
    have := h.lower y
    rw [hM, neg_mulVec, dotProduct_neg, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul]
    linarith
  have key := sq_norm_mulVec_le h.1 (by linarith) hMc x
  have hMx : M *ᵥ x = -(A *ᵥ x) - a • x := by
    rw [hM, neg_mulVec, add_mulVec, smul_mulVec, one_mulVec, neg_add']
  rw [hMx] at key
  simp only [sub_dotProduct, dotProduct_sub, neg_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at key
  rw [dotProduct_comm (A *ᵥ x) x] at key
  nlinarith [key]

/-- `A - s I` is invertible for `s > 0` when `-b ≤ A ≤ -a < 0`. -/
theorem SpecIn.isUnit_det_sub (h : SpecIn A a b) (ha : 0 < a) {s : ℝ} (hs : 0 ≤ s) :
    IsUnit (A - s • (1 : Matrix m m ℝ)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : v ⬝ᵥ ((A - s • (1 : Matrix m m ℝ)) *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at h1
  have h2 := h.upper v
  have h3 : 0 < v ⬝ᵥ v := by
    rcases (dotProduct_self_star_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
  nlinarith

/-- The Cayley-type contraction factor `δ(a, b) = (√b - √a)/(√b + √a)`. -/
noncomputable def cayleyRate (a b : ℝ) : ℝ := (√b - √a) / (√b + √a)

theorem cayleyRate_nonneg {a b : ℝ} (hab : a ≤ b) : 0 ≤ cayleyRate a b :=
  div_nonneg (by linarith [Real.sqrt_le_sqrt hab]) (by positivity)

theorem cayleyRate_lt_one {a b : ℝ} (ha : 0 < a) : cayleyRate a b < 1 := by
  have := Real.sqrt_pos.mpr ha
  rw [cayleyRate, div_lt_one (by positivity)]
  linarith

/-- The scalar inequality behind the Cayley bound. -/
private theorem cayley_scalar {P Q R α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (key : P + α ^ 2 * β ^ 2 * R ≤ (α ^ 2 + β ^ 2) * (-Q)) :
    P + 2 * (α * β) * Q + (α * β) ^ 2 * R ≤
      ((β - α) / (β + α)) ^ 2 * (P - 2 * (α * β) * Q + (α * β) ^ 2 * R) := by
  have hpos : 0 < (β + α) ^ 2 := by positivity
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hpos]
  have h1 : 0 ≤ α * β * (-(P + (α ^ 2 + β ^ 2) * Q + α ^ 2 * β ^ 2 * R)) :=
    mul_nonneg (mul_pos hα hβ).le (by linarith)
  have h2 : (β - α) ^ 2 * (P - 2 * (α * β) * Q + (α * β) ^ 2 * R) -
      (P + 2 * (α * β) * Q + (α * β) ^ 2 * R) * (β + α) ^ 2 =
      4 * (α * β * (-(P + (α ^ 2 + β ^ 2) * Q + α ^ 2 * β ^ 2 * R))) := by ring
  linarith

/-- **The Cayley bound.**  For symmetric `A` with `-b ≤ A ≤ -a < 0` and `s = √(ab)`,
`‖(A + s) x‖ ≤ δ ‖(A - s) x‖` with `δ = (√b - √a)/(√b + √a)`. -/
theorem SpecIn.sq_norm_add_le (h : SpecIn A a b) (ha : 0 < a) (hab : a ≤ b) (x : m → ℝ) :
    ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) ⬝ᵥ ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) ≤
      cayleyRate a b ^ 2 * (((A - √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) ⬝ᵥ
        ((A - √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x)) := by
  have key := h.sq_norm_mulVec_add_le hab x
  have hb : 0 < b := ha.trans_le hab
  have hα0 : 0 < √a := Real.sqrt_pos.mpr ha
  have hβ0 : 0 < √b := Real.sqrt_pos.mpr hb
  have hsq : √(a * b) = √a * √b := Real.sqrt_mul ha.le b
  have ha' : √a ^ 2 = a := Real.sq_sqrt ha.le
  have hb' : √b ^ 2 = b := Real.sq_sqrt hb.le
  have e1 : ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) ⬝ᵥ
      ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) =
      (A *ᵥ x) ⬝ᵥ (A *ᵥ x) + 2 * (√a * √b) * (x ⬝ᵥ (A *ᵥ x)) + (√a * √b) ^ 2 * (x ⬝ᵥ x) := by
    simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsq, dotProduct_comm (A *ᵥ x) x]
    ring
  have e2 : ((A - √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) ⬝ᵥ
      ((A - √(a * b) • (1 : Matrix m m ℝ)) *ᵥ x) =
      (A *ᵥ x) ⬝ᵥ (A *ᵥ x) - 2 * (√a * √b) * (x ⬝ᵥ (A *ᵥ x)) + (√a * √b) ^ 2 * (x ⬝ᵥ x) := by
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsq, dotProduct_comm (A *ᵥ x) x]
    ring
  rw [e1, e2, cayleyRate]
  refine cayley_scalar hα0 hβ0 ?_
  rw [ha', hb']
  linarith [key]

end Symmetric

/-! ### Sylvester equations with symmetric coefficients: explicit decay -/

section Lyapunov

variable {A : Matrix m m ℝ} {B : Matrix n n ℝ} {C X : Matrix m n ℝ} {a b : ℝ}

/-- The Cayley factor `F(A, s) = (A + s)(A - s)⁻¹`. -/
noncomputable def cayley (A : Matrix m m ℝ) (s : ℝ) : Matrix m m ℝ :=
  (A + s • 1) * (A - s • 1)⁻¹

/-- `‖(A + s)(A - s)⁻¹‖₂ ≤ δ(a, b)` for symmetric `-b ≤ A ≤ -a < 0`, `s = √(ab)`. -/
theorem SpecIn.specNorm_cayley_le (h : SpecIn A a b) (ha : 0 < a) (hab : a ≤ b) :
    specNorm (cayley A √(a * b)) ≤ cayleyRate a b := by
  refine specNorm_le_of (cayleyRate_nonneg hab) fun x => ?_
  have hdet := h.isUnit_det_sub ha (Real.sqrt_nonneg (a * b))
  set y : m → ℝ := (A - √(a * b) • (1 : Matrix m m ℝ))⁻¹ *ᵥ x.ofLp with hy
  have hy' : (A - √(a * b) • (1 : Matrix m m ℝ)) *ᵥ y = x.ofLp := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have h1 : ‖toEuclideanLin (cayley A √(a * b)) x‖ ^ 2 =
      ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ y) ⬝ᵥ ((A + √(a * b) • (1 : Matrix m m ℝ)) *ᵥ y) := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      toLpLin_apply, WithLp.ofLp_toLp, cayley, ← mulVec_mulVec, ← hy]
  have h2 : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
    simp
  have key := h.sq_norm_add_le ha hab y
  rw [hy'] at key
  have h3 : ‖toEuclideanLin (cayley A √(a * b)) x‖ ^ 2 ≤ (cayleyRate a b * ‖x‖) ^ 2 := by
    rw [mul_pow, h1, h2]; exact key
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (cayleyRate_nonneg hab) (norm_nonneg _)) two_ne_zero).mp h3

/-- Constant shifts `p ≡ s`, `q ≡ -s` turn `r_k(A)` into the power `F(A, s)^k`. -/
theorem ratA_const (A : Matrix m m ℝ) (s : ℝ) (k : ℕ) :
    ratA A (fun _ => s) (fun _ => -s) k = cayley A s ^ k := by
  induction k with
  | zero => simp [ratA]
  | succ k ih => rw [pow_succ', ← ih]; simp [ratA, cayley, neg_smul, sub_neg_eq_add]

theorem ratB_const (B : Matrix n n ℝ) (s : ℝ) (k : ℕ) :
    ratB B (fun _ => s) (fun _ => -s) k = cayley B s ^ k := by
  induction k with
  | zero => simp [ratB]
  | succ k ih => rw [pow_succ, ← ih]; simp [ratB, cayley, neg_smul, ← sub_eq_add_neg]

theorem specNorm_pow_le {F : Matrix m m ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hF : specNorm F ≤ δ) (k : ℕ) :
    specNorm (F ^ k) ≤ δ ^ k := by
  induction k with
  | zero => simpa using specNorm_one_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (specNorm_mul_le _ _).trans (mul_le_mul ih hF (specNorm_nonneg _) (pow_nonneg hδ k))

/-- **Explicit singular-value decay for symmetric Sylvester equations.**  If `A X + X B = C`
with symmetric `A`, `B` whose spectra lie in `[-b, -a]`, `0 < a ≤ b`, then for every `k`
`σ_{k rank C}(X) ≤ δ^{2k} ‖X‖₂`, `δ = (√b - √a)/(√b + √a) = (√κ - 1)/(√κ + 1)`, `κ = b/a`.
For `k = 1` this is Penzl's one-shift bound (sharp for the single Cayley factor); for `k ≥ 2`
Penzl's and the Zolotarev bounds (Beckermann–Townsend) are stronger: the present bound repeats
the optimal single shift `√(ab)` and only uses submultiplicativity.  Non-asymptotic, explicit
constants, no SVD of `X` needed. -/
theorem singularValues_le_cayleyRate_pow (hX : A * X + X * B = C) (hA : SpecIn A a b)
    (hB : SpecIn B a b) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    (toEuclideanLin X).singularValues (k * C.rank) ≤ cayleyRate a b ^ (2 * k) * specNorm X := by
  have hs := Real.sqrt_nonneg (a * b)
  have hp : ∀ j < k, IsUnit (A - (fun _ : ℕ => √(a * b)) j • (1 : Matrix m m ℝ)).det :=
    fun _ _ => hA.isUnit_det_sub ha hs
  have hq : ∀ j < k, IsUnit (B + (fun _ : ℕ => -√(a * b)) j • (1 : Matrix n n ℝ)).det := by
    intro _ _
    simpa [neg_smul, sub_eq_add_neg] using hB.isUnit_det_sub ha hs
  have h := singularValues_le hX hp hq
  rw [ratA_const, ratB_const] at h
  have hδ := cayleyRate_nonneg hab
  have h1 := specNorm_pow_le hδ (hA.specNorm_cayley_le ha hab) k
  have h2 := specNorm_pow_le hδ (hB.specNorm_cayley_le ha hab) k
  calc _ ≤ _ := h
    _ ≤ cayleyRate a b ^ k * specNorm X * cayleyRate a b ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (specNorm_nonneg _)) h2 (specNorm_nonneg _)
          (mul_nonneg (pow_nonneg hδ k) (specNorm_nonneg _))
    _ = cayleyRate a b ^ (2 * k) * specNorm X := by ring

/-- Frobenius form: `dist(X, M_{≤ k rank C}) ≤ δ^{2k} ‖X‖_F`. -/
theorem distLR_le_cayleyRate_pow (hX : A * X + X * B = C) (hA : SpecIn A a b)
    (hB : SpecIn B a b) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    distLR (k * C.rank) X ≤ cayleyRate a b ^ (2 * k) * ‖X‖ := by
  have hs := Real.sqrt_nonneg (a * b)
  have hp : ∀ j < k, IsUnit (A - (fun _ : ℕ => √(a * b)) j • (1 : Matrix m m ℝ)).det :=
    fun _ _ => hA.isUnit_det_sub ha hs
  have hq : ∀ j < k, IsUnit (B + (fun _ : ℕ => -√(a * b)) j • (1 : Matrix n n ℝ)).det := by
    intro _ _
    simpa [neg_smul, sub_eq_add_neg] using hB.isUnit_det_sub ha hs
  have h := distLR_le hX hp hq
  rw [ratA_const, ratB_const] at h
  have hδ := cayleyRate_nonneg hab
  have h1 := specNorm_pow_le hδ (hA.specNorm_cayley_le ha hab) k
  have h2 := specNorm_pow_le hδ (hB.specNorm_cayley_le ha hab) k
  calc _ ≤ _ := h
    _ ≤ cayleyRate a b ^ k * ‖X‖ * cayleyRate a b ^ k :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (specNorm_nonneg _)
          (mul_nonneg (pow_nonneg hδ k) (norm_nonneg _))
    _ = cayleyRate a b ^ (2 * k) * ‖X‖ := by ring

/-- The ε-rank consequence: `rank_ε(X) ≤ k rank C` as soon as `δ^{2k} ‖X‖_F ≤ ε`. -/
theorem epsRank_le_of_cayleyRate_pow (hX : A * X + X * B = C) (hA : SpecIn A a b)
    (hB : SpecIn B a b) (ha : 0 < a) (hab : a ≤ b) {k : ℕ} {ε : ℝ}
    (hε : cayleyRate a b ^ (2 * k) * ‖X‖ ≤ ε) : epsRank ε X ≤ k * C.rank :=
  epsRank_le_of_distLR_le ((distLR_le_cayleyRate_pow hX hA hB ha hab k).trans hε)

end Lyapunov

/-! ### The Sylvester flow `Ẋ = A X + X B + C` -/

section Flow

variable {A : Matrix m m ℝ} {B : Matrix n n ℝ} {C : Matrix m n ℝ}

theorem hasDerivAt_mexp (A : Matrix m m ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mexp (s • A)) (mexp (t • A) * A) t := by
  let _ := Matrix.frobeniusNormedRing (m := m) (α := ℝ)
  let _ := Matrix.frobeniusNormedAlgebra (m := m) (α := ℝ) (R := ℝ)
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) A t

theorem hasDerivAt_mexp' (A : Matrix m m ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mexp (s • A)) (A * mexp (t • A)) t := by
  let _ := Matrix.frobeniusNormedRing (m := m) (α := ℝ)
  let _ := Matrix.frobeniusNormedAlgebra (m := m) (α := ℝ) (R := ℝ)
  exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t

theorem mexp_mul_mexp_neg (A : Matrix m m ℝ) (t : ℝ) : mexp (t • A) * mexp (t • (-A)) = 1 := by
  unfold mexp
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).neg_right.smul_left t).smul_right t)]
  simp

theorem mexp_neg_mul_mexp (A : Matrix m m ℝ) (t : ℝ) : mexp (t • (-A)) * mexp (t • A) = 1 := by
  have := mexp_mul_mexp_neg (-A) t
  rwa [neg_neg] at this

/-- **Variation of constants for `Ẏ = A Y + Y B`**: every solution is `Y(t) = e^{tA} Y(0) e^{tB}`.
Proof: `e^{-tA} Y(t) e^{-tB}` has derivative zero. -/
theorem eq_mexp_mul_mexp {Y : ℝ → Matrix m n ℝ}
    (hY : ∀ t, HasDerivAt Y (A * Y t + Y t * B) t) (t : ℝ) :
    Y t = mexp (t • A) * Y 0 * mexp (t • B) := by
  set Z : ℝ → Matrix m n ℝ := fun s => mexp (s • (-A)) * Y s * mexp (s • (-B)) with hZ
  have hZ' : ∀ s, HasDerivAt Z 0 s := by
    intro s
    have h := Frobenius.hasDerivAt_mul_mul (hasDerivAt_mexp (-A) s) (hY s) (hasDerivAt_mexp' (-B) s)
    convert h using 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    abel
  have hc : Z t = Z 0 :=
    is_const_of_deriv_eq_zero (fun s => (hZ' s).differentiableAt) (fun s => (hZ' s).deriv) t 0
  have h0 : Z 0 = Y 0 := by simp [hZ, mexp]
  calc Y t = mexp (t • A) * (mexp (t • (-A)) * Y t * mexp (t • (-B))) * mexp (t • B) := by
        simp only [← Matrix.mul_assoc, mexp_mul_mexp_neg, Matrix.one_mul]
        rw [Matrix.mul_assoc, mexp_neg_mul_mexp, Matrix.mul_one]
    _ = mexp (t • A) * Y 0 * mexp (t • B) := by
        have hZt : mexp (t • -A) * Y t * mexp (t • -B) = Y 0 := hc.trans h0
        rw [hZt]

/-- **The Sylvester flow relative to an equilibrium.**  If `Ẋ = A X + X B + C` and
`A Xeq + Xeq B + C = 0`, then `X(t) - Xeq = e^{tA} (X(0) - Xeq) e^{tB}` for all `t`. -/
theorem sub_eq_mexp_mul_mexp {X : ℝ → Matrix m n ℝ} {Xeq : Matrix m n ℝ}
    (hX : ∀ t, HasDerivAt X (A * X t + X t * B + C) t) (heq : A * Xeq + Xeq * B + C = 0) (t : ℝ) :
    X t - Xeq = mexp (t • A) * (X 0 - Xeq) * mexp (t • B) := by
  have hY : ∀ t, HasDerivAt (fun s => X s - Xeq) (A * (X t - Xeq) + (X t - Xeq) * B) t := by
    intro t
    have h := (hX t).sub_const Xeq
    convert h using 1
    rw [Matrix.mul_sub, Matrix.sub_mul]
    have : A * Xeq + Xeq * B = -C := by rw [← sub_eq_zero, sub_neg_eq_add, heq]
    calc A * X t - A * Xeq + (X t * B - Xeq * B)
        = A * X t + X t * B - (A * Xeq + Xeq * B) := by abel
      _ = A * X t + X t * B + C := by rw [this, sub_neg_eq_add]
  exact eq_mexp_mul_mexp hY t

omit [DecidableEq m] [DecidableEq n] in
/-- **Exact rank bound along the flow**: `rank (X(t) - Xeq) ≤ rank (X(0) - Xeq)` for all `t`
(no stability or normality assumed; the flow acts by invertible factors). -/
theorem rank_sub_le {X : ℝ → Matrix m n ℝ} {Xeq : Matrix m n ℝ}
    (hX : ∀ t, HasDerivAt X (A * X t + X t * B + C) t) (heq : A * Xeq + Xeq * B + C = 0) (t : ℝ) :
    (X t - Xeq).rank = (X 0 - Xeq).rank := by
  classical
  rw [sub_eq_mexp_mul_mexp hX heq t]
  have hA : IsUnit (mexp (t • A)).det := (isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  have hB : IsUnit (mexp (t • B)).det := (isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp (𝔸 := ℝ) _)
  rw [rank_mul_eq_left_of_isUnit_det _ _ hB, rank_mul_eq_right_of_isUnit_det _ _ hA]

omit [DecidableEq m] [DecidableEq n] in
theorem rank_neg' (C : Matrix m n ℝ) : (-C).rank = C.rank := by
  rw [← neg_one_smul ℝ C]
  exact rank_smul_of_mem_nonZeroDivisors C (mem_nonZeroDivisors_of_ne_zero (by norm_num))

/-- **Singular values along the Sylvester flow.**  With `X_k = adi k` for the equilibrium
equation `A Xeq + Xeq B = -C` (rank `≤ k rank C`),
`σ_{rank X(0) + 2 k rank C}(X(t)) ≤ (1 + ‖e^{tA}‖₂ ‖e^{tB}‖₂) ‖r_k(A)‖₂ ‖Xeq‖₂ ‖r_k(-B)⁻¹‖₂`.
The approximant is `X_k + e^{tA} (X(0) - X_k) e^{tB}`.  For symmetric coefficients with spectra
in `[-b, -a]` and constant shifts the rational norms are `≤ δ^k` each (`specNorm_cayley_le`),
and `‖e^{tA}‖₂ ≤ 1` for `t ≥ 0` (`specNorm_mexp_le_one`), giving `2 δ^{2k} ‖Xeq‖₂` uniformly in
`t ≥ 0` (`singularValues_flow_le_cayleyRate_pow`). -/
theorem singularValues_flow_le {X : ℝ → Matrix m n ℝ} {Xeq : Matrix m n ℝ}
    (hX : ∀ t, HasDerivAt X (A * X t + X t * B + C) t) (heq : A * Xeq + Xeq * B + C = 0)
    {p q : ℕ → ℝ} {k : ℕ} (hp : ∀ j < k, IsUnit (A - p j • 1).det)
    (hq : ∀ j < k, IsUnit (B + q j • 1).det) (t : ℝ) :
    (toEuclideanLin (X t)).singularValues ((X 0).rank + 2 * (k * C.rank)) ≤
      (1 + specNorm (mexp (t • A)) * specNorm (mexp (t • B))) *
        (specNorm (ratA A p q k) * specNorm Xeq * specNorm (ratB B p q k)) := by
  have heq' : A * Xeq + Xeq * B = -C := by rw [← sub_eq_zero, sub_neg_eq_add, heq]
  set Xk := adi A B (-C) p q k with hXk
  have hrk : Xk.rank ≤ k * C.rank := by rw [hXk, ← rank_neg' C]; exact rank_adi_le A B (-C) p q k
  have herr : Xeq - Xk = ratA A p q k * Xeq * ratB B p q k := sub_adi_eq heq' hp hq
  set E := mexp (t • A)
  set G := mexp (t • B)
  -- the approximant
  set Y := Xk + E * (X 0 - Xk) * G with hY
  have hrankY : Y.rank ≤ (X 0).rank + 2 * (k * C.rank) := by
    have h1 : (E * (X 0 - Xk) * G).rank ≤ (X 0).rank + k * C.rank := by
      refine ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans ?_
      calc (X 0 - Xk).rank = (X 0 + -Xk).rank := by rw [sub_eq_add_neg]
        _ ≤ (X 0).rank + (-Xk).rank := rank_add_le _ _
        _ ≤ (X 0).rank + k * C.rank := by rw [rank_neg']; gcongr
    calc Y.rank ≤ Xk.rank + (E * (X 0 - Xk) * G).rank := rank_add_le _ _
      _ ≤ k * C.rank + ((X 0).rank + k * C.rank) := add_le_add hrk h1
      _ = (X 0).rank + 2 * (k * C.rank) := by ring
  have hXt : X t = Xeq + E * (X 0 - Xeq) * G := by
    have := sub_eq_mexp_mul_mexp hX heq t
    rw [← this]; abel
  have hdiff : X t - Y = (Xeq - Xk) - E * (Xeq - Xk) * G := by
    rw [hXt, hY]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hnorm : specNorm (X t - Y) ≤ (1 + specNorm E * specNorm G) * specNorm (Xeq - Xk) := by
    rw [hdiff]
    have h1 : specNorm (E * (Xeq - Xk) * G) ≤ specNorm E * specNorm (Xeq - Xk) * specNorm G := by
      refine (specNorm_mul_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    have h2 : specNorm ((Xeq - Xk) - E * (Xeq - Xk) * G) ≤
        specNorm (Xeq - Xk) + specNorm (E * (Xeq - Xk) * G) := by
      rw [sub_eq_add_neg]
      exact (WeylSingular.specNorm_add_le _ _).trans (by rw [WeylSingular.specNorm_neg])
    nlinarith [specNorm_nonneg E, specNorm_nonneg G, specNorm_nonneg (Xeq - Xk)]
  have hres : specNorm (Xeq - Xk) ≤
      specNorm (ratA A p q k) * specNorm Xeq * specNorm (ratB B p q k) := by
    rw [herr]
    refine (specNorm_mul_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
  calc (toEuclideanLin (X t)).singularValues ((X 0).rank + 2 * (k * C.rank))
      ≤ specNorm (X t - Y) := singularValues_le_specNorm_sub _ _ hrankY
    _ ≤ (1 + specNorm E * specNorm G) * specNorm (Xeq - Xk) := hnorm
    _ ≤ _ := mul_le_mul_of_nonneg_left hres
        (by positivity [specNorm_nonneg E, specNorm_nonneg G])

end Flow

/-! ### OP-OT-59: spectral separation alone does not force singular-value decay -/

section Counterexample

/-- The nilpotent Jordan block on `ℝ^{N+1}`: `J i j = 1` iff `j = i + 1`
(so `J e_{j} = e_{j-1}`). -/
def jordan (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- The cyclic shift `K = J + e_N e_0ᵀ`, the permutation matrix of `finRotate`. -/
def cyc (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if j = finRotate (N + 1) i then 1 else 0

/-- The rank-one right-hand side `C = -e_N e_0ᵀ`. -/
def cexC (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  vecMulVec (fun i => if i = Fin.last N then -1 else 0) (fun j => if j = 0 then 1 else 0)

theorem jordan_apply (N : ℕ) (i j : Fin (N + 1)) :
    jordan N i j = if (j : ℕ) = i + 1 then 1 else 0 := rfl

theorem cyc_apply (N : ℕ) (i j : Fin (N + 1)) :
    cyc N i j = if j = finRotate (N + 1) i then 1 else 0 := rfl

theorem cexC_apply (N : ℕ) (i j : Fin (N + 1)) :
    cexC N i j = (if i = Fin.last N then -1 else 0) * (if j = 0 then 1 else 0) := rfl

theorem rank_cexC_le (N : ℕ) : (cexC N).rank ≤ 1 := rank_vecMulVec_le _ _

/-- `X = I` solves the Sylvester equation `J X + X (-K) = C`. -/
theorem jordan_sylvester (N : ℕ) : jordan N * 1 + 1 * (-cyc N) = cexC N := by
  ext i j
  rw [Matrix.mul_one, Matrix.one_mul, Matrix.add_apply, Matrix.neg_apply, jordan_apply, cyc_apply,
    cexC_apply]
  by_cases hi : i = Fin.last N
  · subst hi
    rw [finRotate_last, Fin.val_last]
    have hj : ¬ ((j : ℕ) = N + 1) := by omega
    by_cases hj0 : j = 0 <;> simp [hj, hj0]
  · have h1 : ((finRotate (N + 1) i : Fin (N + 1)) : ℕ) = i + 1 := coe_finRotate_of_ne_last hi
    have h2 : (j = finRotate (N + 1) i) ↔ ((j : ℕ) = i + 1) := by
      rw [Fin.ext_iff, h1]
    rw [if_congr h2 rfl rfl]
    simp [hi]

/-- `K` is orthogonal: `Kᵀ K = 1`. -/
theorem cyc_transpose_mul (N : ℕ) : (cyc N)ᵀ * cyc N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cyc_apply, Matrix.one_apply]
  rw [Fintype.sum_equiv (finRotate (N + 1)) _
    (fun l => (if i = l then (1 : ℝ) else 0) * (if j = l then 1 else 0)) (fun l => rfl)]
  simp

/-- `K` is orthogonal: `K Kᵀ = 1`; with `cyc_transpose_mul`, `K` is normal. -/
theorem cyc_mul_transpose (N : ℕ) : cyc N * (cyc N)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cyc_apply, Matrix.one_apply]
  simp [eq_comm]

/-- `‖K‖₂ ≤ 1`. -/
theorem specNorm_cyc_le (N : ℕ) : specNorm (cyc N) ≤ 1 :=
  specNorm_le_one_of_orthonormal (cyc_transpose_mul N)

/-- Powers of the Jordan block: `(J^k) i j = 1` iff `j = i + k`. -/
theorem jordan_pow (N k : ℕ) :
    jordan N ^ k = Matrix.of fun i j : Fin (N + 1) => if (j : ℕ) = i + k then 1 else 0 := by
  induction k with
  | zero =>
    ext i j
    simp only [pow_zero, Matrix.one_apply, Matrix.of_apply, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · have : (j : ℕ) ≠ i := fun h => hij (Fin.ext h).symm
      simp [hij, this]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, jordan_apply]
    by_cases h : (i : ℕ) + k < N + 1
    · rw [Finset.sum_eq_single (⟨(i : ℕ) + k, h⟩ : Fin (N + 1))]
      · simp [add_assoc]
      · intro l _ hl
        have : (l : ℕ) ≠ i + k := fun h' => hl (Fin.ext h')
        simp [this]
      · simp
    · rw [Finset.sum_eq_zero]
      · have : (j : ℕ) ≠ i + (k + 1) := by omega
        simp [this]
      · intro l _
        have : (l : ℕ) ≠ i + k := by omega
        simp [this]

/-- `J` is nilpotent: `J^{N+1} = 0`, so its spectrum is `{0}`. -/
theorem jordan_pow_eq_zero (N : ℕ) : jordan N ^ (N + 1) = 0 := by
  rw [jordan_pow]
  ext i j
  have : (j : ℕ) ≠ i + (N + 1) := by omega
  simp [this]

/-- `J = K D` with `D` the orthogonal projector `diag(0, 1, …, 1)`. -/
theorem jordan_eq_cyc_mul (N : ℕ) :
    jordan N = cyc N * diagonal (fun j : Fin (N + 1) => if j = 0 then 0 else 1) := by
  ext i j
  rw [Matrix.mul_diagonal, jordan_apply, cyc_apply]
  by_cases hi : i = Fin.last N
  · subst hi
    rw [finRotate_last, Fin.val_last]
    have hj : ¬ ((j : ℕ) = N + 1) := by omega
    by_cases hj0 : j = 0 <;> simp [hj, hj0]
  · have h1 : ((finRotate (N + 1) i : Fin (N + 1)) : ℕ) = i + 1 := coe_finRotate_of_ne_last hi
    have h2 : (j = finRotate (N + 1) i) ↔ ((j : ℕ) = i + 1) := by
      rw [Fin.ext_iff, h1]
    have h3 : (j : ℕ) = i + 1 → j ≠ 0 := by
      intro h h0; rw [h0] at h; simp at h
    rw [if_congr h2 rfl rfl]
    by_cases ha : (j : ℕ) = i + 1
    · simp [ha, h3 ha]
    · simp [ha]

/-- `‖J‖₂ ≤ 1`. -/
theorem specNorm_jordan_le (N : ℕ) : specNorm (jordan N) ≤ 1 := by
  rw [jordan_eq_cyc_mul]
  have hD : IsOrthProjMat (diagonal (fun j : Fin (N + 1) => if j = 0 then (0 : ℝ) else 1)) :=
    ⟨diagonal_transpose _, by
      rw [diagonal_mul_diagonal]
      congr 1; ext j; split_ifs <;> simp⟩
  calc specNorm (cyc N * diagonal fun j : Fin (N + 1) => if j = 0 then (0 : ℝ) else 1)
      ≤ specNorm (cyc N) *
          specNorm (diagonal fun j : Fin (N + 1) => if j = 0 then (0 : ℝ) else 1) :=
        specNorm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (specNorm_cyc_le N) hD.specNorm_le_one (specNorm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The identity has no singular-value decay at all: `σ_r(I) = 1` for every `r ≤ N`. -/
theorem singularValues_one (N : ℕ) {r : ℕ} (hr : r ≤ N) :
    (toEuclideanLin (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)).singularValues r = 1 := by
  apply le_antisymm
  · calc (toEuclideanLin (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)).singularValues r
        ≤ (toEuclideanLin (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)).singularValues 0 :=
          LinearMap.singularValues_antitone _ (Nat.zero_le r)
      _ = specNorm (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :=
          (specNorm_eq_singularValues_zero _).symm
      _ ≤ 1 := specNorm_one_le
  · rw [← specNorm_sub_truncation]
    set T := truncation (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) r
    have hT : T.rank < Fintype.card (Fin (N + 1)) := by
      rw [Fintype.card_fin]; exact lt_of_le_of_lt (rank_truncation_le _ r) (by omega)
    obtain ⟨x, hx0, hTx⟩ := exists_mulVec_eq_zero_of_rank_lt hT
    have h1 : toEuclideanLin (1 - T) (WithLp.toLp 2 x) = WithLp.toLp 2 x := by
      rw [toLpLin_apply, WithLp.ofLp_toLp, sub_mulVec, hTx, one_mulVec, sub_zero]
    have h2 := norm_toEuclideanLin_le (1 - T) (WithLp.toLp 2 x)
    rw [h1] at h2
    have hx : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (N + 1)))‖ := by
      rw [norm_pos_iff]
      intro h; apply hx0
      have := congrArg WithLp.ofLp h
      simpa using this
    exact le_of_mul_le_mul_right (by simpa using h2) hx

/-- Frobenius form: `dist(I, M_{≤ r}) ≥ 1` for every `r ≤ N`. -/
theorem one_le_distLR_one (N : ℕ) {r : ℕ} (hr : r ≤ N) :
    1 ≤ distLR r (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) := by
  refine le_distLR_of_le_mulVec (by rw [Fintype.card_fin]; omega) zero_le_one fun x => ?_
  simp

/-- **The normal comparison.**  Replacing the Jordan block by the normal matrix `0` with the same
spectrum `{0}` gives a solution of exact rank `≤ 1`. -/
theorem rank_le_one_of_normal_comparison (N : ℕ) {X : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hX : 0 * X + X * (-cyc N) = cexC N) : X.rank ≤ 1 := by
  have h : X = cexC N * (-(cyc N)ᵀ) := by
    rw [← hX, Matrix.zero_mul, zero_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_neg, Matrix.mul_neg, neg_neg, cyc_mul_transpose, Matrix.mul_one]
  rw [h]
  exact (rank_mul_le_left _ _).trans (rank_cexC_le N)

/-- **Counterexample to the unconditional conjecture OP-OT-59.**  For every `N`, the Sylvester
equation `A X + X B = C` with `A = J` (nilpotent Jordan block, spectrum `{0}`, `‖A‖₂ ≤ 1`),
`B = -K` (`K` orthogonal, spectrum on the unit circle, `‖B‖₂ ≤ 1`) and the rank-one `C = -e_N e_0ᵀ`
has the unique solution `X = I`, whose singular values are all equal to `1 = ‖X‖₂`.  The spectra
of `A` and `-B` are separated by distance `1`, the largest value compatible with `‖A‖₂, ‖B‖₂ ≤ 1`,
and yet `σ_r(X)/‖X‖₂ = 1` for all `r ≤ N`.  With the normal matrix `A' = 0` of the same spectrum,
the solution has rank `≤ 1` (`rank_le_one_of_normal_comparison`).  Hence no bound
`σ_{1 + k rank C}(X) ≤ φ(separation, ‖A‖₂, ‖B‖₂, k) ‖X‖₂` with `φ → 0` as `k → ∞` can hold
without a normality (or `κ(V_A)`) assumption; the eigenvector condition number in the
Beckermann–Townsend bound is not removable. -/
theorem conjecture_fails (N : ℕ) :
    jordan N * 1 + 1 * (-cyc N) = cexC N ∧ (cexC N).rank ≤ 1 ∧
    jordan N ^ (N + 1) = 0 ∧ specNorm (jordan N) ≤ 1 ∧
    (cyc N)ᵀ * cyc N = 1 ∧ cyc N * (cyc N)ᵀ = 1 ∧
    ∀ r ≤ N, (toEuclideanLin (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)).singularValues r = 1 :=
  ⟨jordan_sylvester N, rank_cexC_le N, jordan_pow_eq_zero N, specNorm_jordan_le N,
    cyc_transpose_mul N, cyc_mul_transpose N, fun _ hr => singularValues_one N hr⟩

end Counterexample

/-! ### Dissipative coefficients: the flow is a contraction, uniform-in-time rank bound -/

section Contraction

open scoped RealInnerProductSpace

variable {A : Matrix m m ℝ} {B : Matrix n n ℝ} {C : Matrix m n ℝ} {a b : ℝ}

theorem SpecIn.dissipative (h : SpecIn A a b) (ha : 0 ≤ a) (x : m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ 0 := by
  have h0 : 0 ≤ x ⬝ᵥ x := dotProduct_self_star_nonneg x
  exact (h.upper x).trans (by nlinarith)

/-- The Frobenius norm of a one-column matrix is the Euclidean norm of the column. -/
private theorem sq_norm_col (M : Matrix m m ℝ) (x : EuclideanSpace ℝ m) :
    ‖M * Matrix.of (fun i (_ : Fin 1) => x.ofLp i)‖ ^ 2 = ‖toEuclideanLin M x‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_one, toLpLin_apply, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_apply, mulVec, dotProduct]

/-- **Dissipative flows are contractions**: if `⟨A x, x⟩ ≤ 0` for all `x`, then
`‖e^{tA}‖₂ ≤ 1` for `t ≥ 0` (energy estimate `d/ds ‖e^{sA} x‖² = 2 ⟨A e^{sA} x, e^{sA} x⟩ ≤ 0`). -/
theorem specNorm_mexp_le_one (hA : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    specNorm (mexp (t • A)) ≤ 1 := by
  refine specNorm_le_of zero_le_one fun x => ?_
  set X0 : Matrix m (Fin 1) ℝ := Matrix.of (fun i (_ : Fin 1) => x.ofLp i) with hX0
  set y : ℝ → Matrix m (Fin 1) ℝ := fun s => mexp (s • A) * X0 with hy
  have hyd : ∀ s, HasDerivAt y (A * y s) s := fun s => by
    have := Frobenius.hasDerivAt_mul_const X0 (hasDerivAt_mexp' A s)
    simpa [hy, Matrix.mul_assoc] using this
  have hv : ∀ s, ⟪A * y s, y s⟫ ≤ 0 * ‖y s‖ ^ 2 := by
    intro s
    rw [zero_mul, Frobenius.inner_def]
    have := hA (fun i => y s i 0)
    simp only [dotProduct, mulVec] at this
    simpa [Fin.sum_univ_one, Matrix.mul_apply, dotProduct, mul_comm] using this
  have hbound := norm_le_exp_of_inner_deriv_le (a := 0) (b := t) (ℓ := 0) (y := y)
    (v := fun s => A * y s) (fun s _ => (hyd s).continuousAt.continuousWithinAt)
    (fun s _ => (hyd s).hasDerivWithinAt) (fun s _ => hv s) t ⟨ht, le_rfl⟩
  simp only [zero_mul, sub_zero, Real.exp_zero, one_mul] at hbound
  have h0 : y 0 = X0 := by simp [hy, mexp]
  rw [h0] at hbound
  have h1 : ‖y t‖ ^ 2 = ‖toEuclideanLin (mexp (t • A)) x‖ ^ 2 := sq_norm_col _ x
  have h2 : ‖X0‖ ^ 2 = ‖x‖ ^ 2 := by
    have := sq_norm_col (1 : Matrix m m ℝ) x
    simpa [hX0] using this
  have h3 : ‖toEuclideanLin (mexp (t • A)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← h1, ← h2]; exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

/-- **Uniform-in-time ε-rank bound for the Sylvester flow with symmetric negative definite
coefficients.**  If `Ẋ = A X + X B + C`, `A Xeq + Xeq B + C = 0`, `A`, `B` symmetric with spectra in
`[-b, -a]`, `0 < a ≤ b`, then for all `t ≥ 0` and all `k`
`σ_{rank X(0) + 2 k rank C}(X(t)) ≤ 2 δ^{2k} ‖Xeq‖₂`, `δ = (√b - √a)/(√b + √a)`.
The rank-`rank X(0)` part is exact (transported initial data), the `2 k rank C` part is the
equilibrium's ADI approximant and its transport. -/
theorem singularValues_flow_le_cayleyRate_pow {X : ℝ → Matrix m n ℝ} {Xeq : Matrix m n ℝ}
    (hX : ∀ t, HasDerivAt X (A * X t + X t * B + C) t) (heq : A * Xeq + Xeq * B + C = 0)
    (hA : SpecIn A a b) (hB : SpecIn B a b) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (toEuclideanLin (X t)).singularValues ((X 0).rank + 2 * (k * C.rank)) ≤
      2 * cayleyRate a b ^ (2 * k) * specNorm Xeq := by
  have hs := Real.sqrt_nonneg (a * b)
  have hp : ∀ j < k, IsUnit (A - (fun _ : ℕ => √(a * b)) j • (1 : Matrix m m ℝ)).det :=
    fun _ _ => hA.isUnit_det_sub ha hs
  have hq : ∀ j < k, IsUnit (B + (fun _ : ℕ => -√(a * b)) j • (1 : Matrix n n ℝ)).det := by
    intro _ _
    simpa [neg_smul, sub_eq_add_neg] using hB.isUnit_det_sub ha hs
  have h := singularValues_flow_le hX heq hp hq t
  rw [ratA_const, ratB_const] at h
  have hδ := cayleyRate_nonneg hab
  have h1 := specNorm_pow_le hδ (hA.specNorm_cayley_le ha hab) k
  have h2 := specNorm_pow_le hδ (hB.specNorm_cayley_le ha hab) k
  have hE := specNorm_mexp_le_one (hA.dissipative ha.le) ht
  have hG := specNorm_mexp_le_one (hB.dissipative ha.le) ht
  have hEG : 1 + specNorm (mexp (t • A)) * specNorm (mexp (t • B)) ≤ 2 := by
    nlinarith [specNorm_nonneg (mexp (t • A)), specNorm_nonneg (mexp (t • B))]
  have hprod : specNorm (cayley A √(a * b) ^ k) * specNorm Xeq * specNorm (cayley B √(a * b) ^ k)
      ≤ cayleyRate a b ^ k * specNorm Xeq * cayleyRate a b ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right h1 (specNorm_nonneg _)) h2 (specNorm_nonneg _)
      (mul_nonneg (pow_nonneg hδ k) (specNorm_nonneg _))
  calc _ ≤ _ := h
    _ ≤ 2 * (cayleyRate a b ^ k * specNorm Xeq * cayleyRate a b ^ k) :=
        mul_le_mul hEG hprod
          (mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)) (specNorm_nonneg _))
          zero_le_two
    _ = 2 * cayleyRate a b ^ (2 * k) * specNorm Xeq := by ring

end Contraction

end LeanDLRA.Novel.OpRA44

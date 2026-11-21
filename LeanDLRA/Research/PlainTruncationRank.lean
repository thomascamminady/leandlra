import LeanDLRA.Research.DynamicRecompression

/-!
# Ranks of the truncated backward Euler run against the untruncated run

Setting: the Sylvester problem `A' = -(P A + A Q) + F` with `P, Q ⪰ 0`,
`a = λ_min(P) + λ_min(Q) > 0`, backward Euler with step `h`, and the scheme that truncates the
singular value decomposition of every step at the Frobenius tolerance `θ`
(`Y_{j+1} = T_θ(Ŷ_{j+1})`, `Ŷ_{j+1}` the backward Euler step from `Y_j`). `X_j` is the
untruncated run with `X_0 = Y_0`. The error satisfies `‖Y_j - X_j‖ ≤ θ (1 + h a) / (h a)`, and for
scalar problems `rank Y_j ≤ rank_δ(X_j)` with `δ = θ h a / (1 + h a)`. This file settles what
remains of that comparison for matrices, with `P = Q = 1/2` (so `a = 1`) and `θ = 1`.

## It fails for decoupled modes with every step size

`exists_plain_rank_gt_epsRank_mul_step_fraction`: for every `h > 0` there are diagonal `2 × 2`
data and a factor `1/2 < κ < 1` such that `Y_3` has rank one while `‖X_3‖ ≤ κ θ h / (1 + h)`.
Two modes are removed in different steps (the first uses the whole tolerance, the second shares
it with the returning first mode), so that the accumulated error exceeds `θ` when both modes
are released in the third step. That family lies on a tie (`‖Ŷ_2‖ = θ`); the example after
`exists_plain_rank_gt_epsRank_of_params` is an instance with `h = 1/4` and no ties.

## One instance where it fails with every tolerance

`exists_plain_rank_gt_rank`: with `h = 1/9` there are `2 × 2` data such that `Y_3` has rank two
while `X_3` has rank one exactly. Hence `rank Y_3 > rank_δ(X_3)` for every `δ ≥ 0`: at this step
size no positive fraction of the tolerance repairs the comparison. Here `P` and `Q` are
multiples of the identity; what has no common singular basis is the pair `(X_0, F)`. The
singular vectors of the first two truncated steps are rotated against each other; the two
removed parts add up to a matrix whose smallest singular value exceeds the tolerance.

## It holds for decoupled modes with a sign condition

If `P`, `Q`, `F` and the iterates are diagonal, the truncation removes diagonal entries (a
hypothesis: on ties the truncated singular value decomposition of a diagonal matrix need not be
diagonal), and every mode starts between zero and the untruncated run on the side of its
forcing (for instance `X_0 = Y_0 = 0`), then every entry of `Ŷ_j` is dominated by the entry of
`X_j` (`abs_le_abs_of_decoupled_run`), all low-rank distances of `Ŷ_j` are at most those of
`X_j` (`distLR_diagonal_le_of_abs_le`), and `rank Y_j ≤ rank_θ(X_j)` with the full tolerance
(`rank_le_epsRank_of_decoupled_run`). The first counterexample starts on the other side of zero.

The truncation is `EckartYoung.truncation` at the rank `epsRank θ`, as in
`LeanDLRA.DynamicRecompression`; for `2 × 2` matrices `U diag(a, b) Vᵀ` with `|b| < |a|` it is
computed by `truncation_one_mul_diagonal_mul_transpose` (uniqueness of the best approximation of
rank one).
-/

open scoped Matrix LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA.PlainTruncationRank

open LeanDLRA.EckartYoung

/-! ### `θ`-rank one; the backward Euler step with `P = Q = 1/2` -/

section Tools

variable {m n : Type*} [Fintype m] [Fintype n]

/-- If a matrix of rank at most one is within `θ` of `X` and `θ < ‖X‖`, the `θ`-rank of `X`
is one. -/
theorem epsRank_eq_one_of_norm_sub_le {X W : Matrix m n ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hW : W.rank ≤ 1) (h : ‖X - W‖ ≤ θ) (hX : θ < ‖X‖) : epsRank θ X = 1 := by
  refine le_antisymm (epsRank_le_of_norm_sub_le hW h) ?_
  by_contra hlt
  have h0 : epsRank θ X = 0 := by omega
  exact absurd ((epsRank_eq_zero_iff hθ).mp h0) (not_le.mpr hX)

/-- A backward Euler step of the Sylvester equation with `P = Q = 1/2`. -/
theorem add_smul_half_sylvester [DecidableEq n] {h : ℝ} {X X' F : Matrix n n ℝ}
    (hX : (1 + h) • X' = X + h • F) :
    X' + h • (((1 / 2 : ℝ) • (1 : Matrix n n ℝ)) * X' + X' * ((1 / 2 : ℝ) • (1 : Matrix n n ℝ)))
      = X + h • F := by
  rw [← hX]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  module

end Tools

/-! ### Truncation of `2 × 2` matrices with a known singular value decomposition -/

section TwoByTwo

/-- The squared Frobenius norm of `diag(a, b)`. -/
theorem norm_sq_diagonal_two (a b : ℝ) :
    ‖(diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_diagonal]
  simp [Fin.sum_univ_two]

/-- `‖diag(a, b)‖ ≤ r` if `a² + b² ≤ r²`. -/
theorem norm_diagonal_two_le {a b r : ℝ} (hr : 0 ≤ r) (h : a ^ 2 + b ^ 2 ≤ r ^ 2) :
    ‖(diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ r := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).mp ?_
  rw [norm_sq_diagonal_two]
  exact h

/-- `r < ‖diag(a, b)‖` if `r² < a² + b²`. -/
theorem lt_norm_diagonal_two {a b r : ℝ} (hr : 0 ≤ r) (h : r ^ 2 < a ^ 2 + b ^ 2) :
    r < ‖(diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
  refine (pow_lt_pow_iff_left₀ hr (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_sq_diagonal_two]
  exact h

/-- `diag(a, 0)` has rank at most one. -/
theorem rank_diagonal_two_le_one (a : ℝ) :
    (diagonal ![a, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1 := by
  have h : (diagonal ![a, 0] : Matrix (Fin 2) (Fin 2) ℝ) = vecMulVec ![1, 0] ![a, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply]
  rw [h]
  exact rank_vecMulVec_le _ _

/-- **Uniqueness of the best approximation of rank one of `diag(a, b)`, `|b| < |a|`.** A matrix
of rank at most one within `|b|` of `diag(a, b)` is `diag(a, 0)`. -/
theorem eq_diagonal_of_rank_le_one_of_norm_sub_le {a b : ℝ} (hab : |b| < |a|)
    {Z : Matrix (Fin 2) (Fin 2) ℝ} (hZ : Z.rank ≤ 1) (h : ‖diagonal ![a, b] - Z‖ ≤ |b|) :
    Z = diagonal ![a, 0] := by
  obtain ⟨x, hx0, hZx⟩ := exists_mulVec_eq_zero_of_rank_lt (Z := Z)
    (lt_of_le_of_lt hZ (by simp))
  have h0 : Z 0 0 * x 0 + Z 0 1 * x 1 = 0 := by
    have := congrFun hZx 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h1 : Z 1 0 * x 0 + Z 1 1 * x 1 = 0 := by
    have := congrFun hZx 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hn : (a - Z 0 0) ^ 2 + Z 0 1 ^ 2 + (Z 1 0 ^ 2 + (b - Z 1 1) ^ 2) ≤ b ^ 2 := by
    have h2 : ‖diagonal ![a, b] - Z‖ ^ 2 ≤ |b| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [sq_abs, Frobenius.norm_sq_eq_sum] at h2
    simpa [Fin.sum_univ_two] using h2
  have hab2 : b ^ 2 < a ^ 2 := by
    rw [← sq_abs b, ← sq_abs a]
    exact pow_lt_pow_left₀ hab (abs_nonneg _) two_ne_zero
  have c1 : (a * x 0) ^ 2 ≤ ((a - Z 0 0) ^ 2 + Z 0 1 ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by
    have e : a * x 0 = (a - Z 0 0) * x 0 - Z 0 1 * x 1 := by linarith
    rw [e]
    nlinarith [sq_nonneg ((a - Z 0 0) * x 1 + Z 0 1 * x 0)]
  have c2 : (b * x 1) ^ 2 ≤ (Z 1 0 ^ 2 + (b - Z 1 1) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by
    have e : b * x 1 = (b - Z 1 1) * x 1 - Z 1 0 * x 0 := by linarith
    rw [e]
    nlinarith [sq_nonneg ((b - Z 1 1) * x 0 + Z 1 0 * x 1)]
  have hx00 : x 0 = 0 := by
    have hS : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hn hS
    have h4 : (a ^ 2 - b ^ 2) * x 0 ^ 2 ≤ 0 := by nlinarith
    have h5 : x 0 ^ 2 ≤ 0 := by
      by_contra hne
      have := mul_pos (sub_pos.mpr hab2) (not_le.mp hne)
      linarith
    exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h5 (sq_nonneg _))
  have hx1 : x 1 ≠ 0 := by
    intro h1'
    apply hx0
    funext i
    fin_cases i
    · simpa using hx00
    · simpa using h1'
  rw [hx00, mul_zero, zero_add] at h0 h1
  have z01 : Z 0 1 = 0 := (mul_eq_zero.mp h0).resolve_right hx1
  have z11 : Z 1 1 = 0 := (mul_eq_zero.mp h1).resolve_right hx1
  rw [z01, z11] at hn
  have s1 : (a - Z 0 0) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (Z 1 0)]
  have s2 : Z 1 0 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (a - Z 0 0)]
  have z00 : Z 0 0 = a := by
    have := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm s1 (sq_nonneg _))
    linarith
  have z10 : Z 1 0 = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm s2 (sq_nonneg _))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z00, z01, z10, z11]

variable {U V : Matrix (Fin 2) (Fin 2) ℝ} {a b θ : ℝ}

/-- `‖U diag(a, b) Vᵀ - U diag(a, 0) Vᵀ‖ = |b|` for orthogonal `U`, `V`. -/
theorem norm_mul_diagonal_mul_transpose_sub (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a b : ℝ) :
    ‖U * diagonal ![a, b] * Vᵀ - U * diagonal ![a, 0] * Vᵀ‖ = |b| := by
  have e : U * diagonal ![a, b] * Vᵀ - U * diagonal ![a, 0] * Vᵀ
      = U * diagonal ![0, b] * Vᵀ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
  have h2 : ‖(diagonal ![0, b] : Matrix (Fin 2) (Fin 2) ℝ)‖ ^ 2 = |b| ^ 2 := by
    rw [norm_sq_diagonal_two, sq_abs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

/-- **The truncation of rank one of `U diag(a, b) Vᵀ`**, `U`, `V` orthogonal and `|b| < |a|`,
is `U diag(a, 0) Vᵀ`. -/
theorem truncation_one_mul_diagonal_mul_transpose (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hab : |b| < |a|) :
    truncation (U * diagonal ![a, b] * Vᵀ) 1 = U * diagonal ![a, 0] * Vᵀ := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  have hW : (U * diagonal ![a, 0] * Vᵀ).rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (rank_diagonal_two_le_one a))
  have hd := norm_mul_diagonal_mul_transpose_sub hU hV a b
  obtain ⟨M, hM⟩ : ∃ M, M = U * diagonal ![a, b] * Vᵀ := ⟨_, rfl⟩
  rw [← hM] at hd ⊢
  have h1 : ‖M - truncation M 1‖ ≤ |b| := (norm_sub_truncation_le M hW).trans hd.le
  have hZr : (Uᵀ * truncation M 1 * V).rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (rank_truncation_le M 1))
  have hD : Uᵀ * M * V = diagonal ![a, b] := by
    have e : Uᵀ * (U * diagonal ![a, b] * Vᵀ) * V = Uᵀ * U * diagonal ![a, b] * (Vᵀ * V) := by
      simp only [Matrix.mul_assoc]
    rw [hM, e, hU, hV, Matrix.one_mul, Matrix.mul_one]
  have h2 : diagonal ![a, b] - Uᵀ * truncation M 1 * V
      = Uᵀ * (M - truncation M 1) * (Vᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul, hD]
  have h3 : ‖diagonal ![a, b] - Uᵀ * truncation M 1 * V‖ ≤ |b| := by
    rw [h2, Frobenius.norm_mul_transpose_of_orthonormal (by rwa [Matrix.transpose_transpose]),
      Frobenius.norm_mul_of_orthonormal (by rwa [Matrix.transpose_transpose])]
    exact h1
  have h4 := eq_diagonal_of_rank_le_one_of_norm_sub_le hab hZr h3
  calc truncation M 1 = U * Uᵀ * truncation M 1 * (V * Vᵀ) := by
        rw [hU', hV', Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᵀ * truncation M 1 * V) * Vᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal ![a, 0] * Vᵀ := by rw [h4]

/-- The `θ`-rank of `U diag(a, b) Vᵀ` is one if `|b| ≤ θ` and `θ² < a² + b²`. -/
theorem epsRank_mul_diagonal_mul_transpose (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hb : |b| ≤ θ)
    (ha : θ ^ 2 < a ^ 2 + b ^ 2) : epsRank θ (U * diagonal ![a, b] * Vᵀ) = 1 := by
  have hθ : 0 ≤ θ := (abs_nonneg b).trans hb
  refine epsRank_eq_one_of_norm_sub_le hθ (W := U * diagonal ![a, 0] * Vᵀ)
    ((Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (rank_diagonal_two_le_one a))) ?_ ?_
  · rw [norm_mul_diagonal_mul_transpose_sub hU hV]
    exact hb
  · rw [Frobenius.norm_mul_transpose_of_orthonormal hV, Frobenius.norm_mul_of_orthonormal hU]
    exact lt_norm_diagonal_two hθ ha

/-- **Tolerance truncation of `U diag(a, b) Vᵀ`**: if `|b| ≤ θ`, `|b| < |a|` and
`θ² < a² + b²`, the truncated singular value decomposition at the tolerance `θ` is
`U diag(a, 0) Vᵀ`. -/
theorem truncation_epsRank_mul_diagonal_mul_transpose (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hab : |b| < |a|) (hb : |b| ≤ θ) (ha : θ ^ 2 < a ^ 2 + b ^ 2) :
    truncation (U * diagonal ![a, b] * Vᵀ) (epsRank θ (U * diagonal ![a, b] * Vᵀ))
      = U * diagonal ![a, 0] * Vᵀ := by
  rw [epsRank_mul_diagonal_mul_transpose hU hV hb ha,
    truncation_one_mul_diagonal_mul_transpose hU hV hab]

/-- The `θ`-rank of `diag(a, b)` is one if `|b| ≤ θ` and `θ² < a² + b²`. -/
theorem epsRank_diagonal_two (hb : |b| ≤ θ) (ha : θ ^ 2 < a ^ 2 + b ^ 2) :
    epsRank θ (diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  have h := epsRank_mul_diagonal_mul_transpose (U := 1) (V := 1) (by simp) (by simp) hb ha
  simpa using h

/-- Tolerance truncation of `diag(a, b)`: the smaller entry is removed. -/
theorem truncation_epsRank_diagonal_two (hab : |b| < |a|) (hb : |b| ≤ θ)
    (ha : θ ^ 2 < a ^ 2 + b ^ 2) :
    truncation (diagonal ![a, b] : Matrix (Fin 2) (Fin 2) ℝ) (epsRank θ (diagonal ![a, b]))
      = diagonal ![a, 0] := by
  have h := truncation_epsRank_mul_diagonal_mul_transpose (U := 1) (V := 1) (by simp) (by simp)
    hab hb ha
  simpa using h

/-- `s diag(a', b') = diag(a, b) + s diag(g₁, g₂)` entrywise. -/
theorem smul_diagonal_two_eq_add {s a b a' b' g₁ g₂ : ℝ} (h1 : s * a' = a + s * g₁)
    (h2 : s * b' = b + s * g₂) :
    s • (diagonal ![a', b'] : Matrix (Fin 2) (Fin 2) ℝ)
      = diagonal ![a, b] + s • diagonal ![g₁, g₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2]

end TwoByTwo

/-! ### Decoupled modes: a counterexample for every step size -/

section DecoupledCounterexample

/-- **Two decoupled modes, three steps.** For parameters `1/2 < c < κ`, `0 < g < 1/2` with
`c² + g² ≤ 1`, `((1 + h)² + (1 + h)) g ≤ 1` and `(1 + h)² < (c + h κ)² + ((1 + h) g)²` there is
a diagonal `2 × 2` problem with `P = Q = 1/2` such that the run truncated at the tolerance `1`
has rank one in the third step while the untruncated run has norm `κ h / (1 + h)` there.
The first step is `diag(-(1 + h)(c + g₁), -((1 + h)² + (1 + h)) g)` with
`g₁ = (c + h κ) / (1 + h)` and loses its second entry; the second step from the truncated run is
`diag(-c, g)` and is removed; the third is `diag(g₁, g)`, of norm above one, while the
untruncated run is `diag(κ h / (1 + h), 0)`. -/
theorem exists_plain_rank_gt_epsRank_of_params {h c g κ : ℝ} (hh : 0 < h) (hc : 1 / 2 < c)
    (hcκ : c < κ) (hg0 : 0 < g) (hg : g < 1 / 2) (hcg : c ^ 2 + g ^ 2 ≤ 1)
    (ht : ((1 + h) ^ 2 + (1 + h)) * g ≤ 1)
    (h3 : (1 + h) ^ 2 < (c + h * κ) ^ 2 + ((1 + h) * g) ^ 2) :
    ∃ (F : Matrix (Fin 2) (Fin 2) ℝ) (X Y Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      X 0 = Y 0 ∧
      (∀ j < 3, X (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * X (j + 1)
        + X (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) = X j + h • F) ∧
      (∀ j < 3, Yh (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * Yh (j + 1)
        + Yh (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) = Y j + h • F) ∧
      (∀ j < 3, Y (j + 1) = truncation (Yh (j + 1)) (epsRank 1 (Yh (j + 1)))) ∧
      epsRank (κ * (h / (1 + h))) (X 3) = 0 ∧ (Y 3).rank = 1 := by
  have hH : 0 < 1 + h := by linarith
  have hκ0 : 0 < κ := by linarith
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ℝ, (1 + h) * g₁ = c + h * κ :=
    ⟨(c + h * κ) / (1 + h), mul_div_cancel₀ _ hH.ne'⟩
  have hcg₁ : c < g₁ := by
    have h1 : (1 + h) * c < (1 + h) * g₁ := by nlinarith
    exact lt_of_mul_lt_mul_left h1 hH.le
  have e3 : (1 + h) * (κ * (h / (1 + h))) = h * κ := by field_simp
  have hw : 1 < (1 + h) * (c + g₁) := by nlinarith
  have ht0 : 0 < ((1 + h) ^ 2 + (1 + h)) * g := by positivity
  obtain ⟨Gd, hGd⟩ : ∃ Gd : Matrix (Fin 2) (Fin 2) ℝ, Gd = diagonal ![g₁, g] := ⟨_, rfl⟩
  have hF : h • (((1 + h) / h) • Gd) = (1 + h) • Gd := by
    rw [smul_smul]
    congr 1
    field_simp
  obtain ⟨X, hX0, hX1, hX2, hX3⟩ : ∃ X : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      X 0 = diagonal ![(1 + h) * (-((1 + h) * (c + g₁)) - g₁),
        (1 + h) * (-(((1 + h) ^ 2 + (1 + h)) * g) - g)] ∧
      X 1 = diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)] ∧
      X 2 = diagonal ![-c, -((1 + h) * g)] ∧ X 3 = diagonal ![κ * (h / (1 + h)), 0] :=
    ⟨fun j => if j = 0 then diagonal ![(1 + h) * (-((1 + h) * (c + g₁)) - g₁),
        (1 + h) * (-(((1 + h) ^ 2 + (1 + h)) * g) - g)]
      else if j = 1 then diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)]
      else if j = 2 then diagonal ![-c, -((1 + h) * g)] else diagonal ![κ * (h / (1 + h)), 0],
      by simp, by simp, by simp, by simp⟩
  obtain ⟨Y, hY0, hY1, hY2, hY3⟩ : ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      Y 0 = diagonal ![(1 + h) * (-((1 + h) * (c + g₁)) - g₁),
        (1 + h) * (-(((1 + h) ^ 2 + (1 + h)) * g) - g)] ∧
      Y 1 = diagonal ![-((1 + h) * (c + g₁)), 0] ∧ Y 2 = 0 ∧ Y 3 = diagonal ![g₁, 0] :=
    ⟨fun j => if j = 0 then diagonal ![(1 + h) * (-((1 + h) * (c + g₁)) - g₁),
        (1 + h) * (-(((1 + h) ^ 2 + (1 + h)) * g) - g)]
      else if j = 1 then diagonal ![-((1 + h) * (c + g₁)), 0]
      else if j = 2 then 0 else diagonal ![g₁, 0], by simp, by simp, by simp, by simp⟩
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ : ∃ Z : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      Z 1 = diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)] ∧
      Z 2 = diagonal ![-c, g] ∧ Z 3 = diagonal ![g₁, g] :=
    ⟨fun j => if j = 1 then diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)]
      else if j = 2 then diagonal ![-c, g] else diagonal ![g₁, g], by simp, by simp, by simp⟩
  have s01 : (1 + h) • (diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)] :
      Matrix (Fin 2) (Fin 2) ℝ) = diagonal ![(1 + h) * (-((1 + h) * (c + g₁)) - g₁),
        (1 + h) * (-(((1 + h) ^ 2 + (1 + h)) * g) - g)] + (1 + h) • Gd := by
    rw [hGd]
    exact smul_diagonal_two_eq_add (by ring) (by ring)
  have hE1 : epsRank 1 (diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)] :
      Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    refine epsRank_diagonal_two ?_ ?_
    · rw [abs_neg, abs_of_pos ht0]
      exact ht
    · nlinarith [sq_nonneg (((1 + h) ^ 2 + (1 + h)) * g)]
  have hT1 : truncation (diagonal ![-((1 + h) * (c + g₁)), -(((1 + h) ^ 2 + (1 + h)) * g)] :
      Matrix (Fin 2) (Fin 2) ℝ) 1 = diagonal ![-((1 + h) * (c + g₁)), 0] := by
    have h := truncation_one_mul_diagonal_mul_transpose (U := 1) (V := 1)
      (a := -((1 + h) * (c + g₁))) (b := -(((1 + h) ^ 2 + (1 + h)) * g)) (by simp) (by simp)
      (by rw [abs_neg, abs_neg, abs_of_pos ht0, abs_of_pos (by linarith)]; linarith)
    simpa using h
  have hE3 : epsRank 1 (diagonal ![g₁, g] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    refine epsRank_diagonal_two ?_ ?_
    · rw [abs_of_pos hg0]
      linarith
    · rw [← hg₁] at h3
      have h4 : (1 + h) ^ 2 * 1 ^ 2 < (1 + h) ^ 2 * (g₁ ^ 2 + g ^ 2) := by nlinarith
      exact lt_of_mul_lt_mul_left h4 (by positivity)
  have hT3 : truncation (diagonal ![g₁, g] : Matrix (Fin 2) (Fin 2) ℝ) 1 = diagonal ![g₁, 0] := by
    have h := truncation_one_mul_diagonal_mul_transpose (U := 1) (V := 1) (a := g₁) (b := g)
      (by simp) (by simp)
      (by rw [abs_of_pos hg0, abs_of_pos (by linarith)]; linarith)
    simpa using h
  have hE2 : epsRank 1 (diagonal ![-c, g] : Matrix (Fin 2) (Fin 2) ℝ) = 0 :=
    (epsRank_eq_zero_iff zero_le_one).mpr (norm_diagonal_two_le zero_le_one (by nlinarith))
  refine ⟨((1 + h) / h) • Gd, X, Y, Z, by rw [hX0, hY0], ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    apply add_smul_half_sylvester
    rw [hF]
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hX0, hX1]
      exact s01
    · rw [hX1, hX2, hGd]
      exact smul_diagonal_two_eq_add (by linarith) (by ring)
    · rw [hX2, hX3, hGd]
      exact smul_diagonal_two_eq_add (by linarith) (by ring)
  · intro j hj
    apply add_smul_half_sylvester
    rw [hF]
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hY0, hZ1]
      exact s01
    · rw [hY1, hZ2, hGd]
      exact smul_diagonal_two_eq_add (by linarith) (by ring)
    · rw [hY2, hZ3, hGd, zero_add]
  · intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hY1, hZ1, hE1, hT1]
    · rw [hY2, hZ2, hE2, truncation_zero]
    · rw [hY3, hZ3, hE3, hT3]
  · rw [hX3]
    have hε : 0 ≤ κ * (h / (1 + h)) := by positivity
    exact (epsRank_eq_zero_iff hε).mpr (norm_diagonal_two_le hε (by nlinarith))
  · have h3 : Y 3 = truncation (Z 3) (epsRank 1 (Z 3)) := by rw [hY3, hZ3, hE3, hT3]
    rw [h3, DynamicRecompression.rank_truncation_epsRank zero_le_one, hZ3, hE3]

/-- **The comparison with the step fraction of the tolerance fails for every step size.**
For every `h > 0` there are a factor `1/2 < κ < 1` and a diagonal `2 × 2` problem with
`P = Q = 1/2` (so `a = 1`) such that the backward Euler run truncated at the tolerance `θ = 1`
has rank one in the third step while the untruncated run satisfies
`‖X₃‖ ≤ κ θ h a / (1 + h a)`: `rank Y₃ = 1 > 0 = rank_{κ θ h a / (1 + h a)}(X₃)`. The instance
lies on a tie: the second step from the truncated run has norm `‖Ŷ₂‖ = θ` exactly and is
removed. -/
theorem exists_plain_rank_gt_epsRank_mul_step_fraction {h : ℝ} (hh : 0 < h) :
    ∃ (κ : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ) (X Y Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      1 / 2 < κ ∧ κ < 1 ∧ X 0 = Y 0 ∧
      (∀ j < 3, X (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * X (j + 1)
        + X (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) = X j + h • F) ∧
      (∀ j < 3, Yh (j + 1) + h • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * Yh (j + 1)
        + Yh (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) = Y j + h • F) ∧
      (∀ j < 3, Y (j + 1) = truncation (Yh (j + 1)) (epsRank 1 (Yh (j + 1)))) ∧
      epsRank (κ * (h / (1 + h))) (X 3) = 0 ∧ (Y 3).rank = 1 := by
  have hH : 1 < (1 + h) ^ 2 := by nlinarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / (4 * (1 + h) ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu4 : u < 1 / 4 := by
    rw [hu, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hd : 0 < 1 + u ^ 2 := by positivity
  have hc : 1 / 2 < (1 - u ^ 2) / (1 + u ^ 2) := by
    rw [lt_div_iff₀ hd]
    nlinarith
  have hc1 : (1 - u ^ 2) / (1 + u ^ 2) < 1 := by
    rw [div_lt_one hd]
    nlinarith
  have hg0 : 0 < 2 * u / (1 + u ^ 2) := by positivity
  have hg : 2 * u / (1 + u ^ 2) < 1 / 2 := by
    rw [div_lt_iff₀ hd]
    nlinarith
  have hcg : ((1 - u ^ 2) / (1 + u ^ 2)) ^ 2 + (2 * u / (1 + u ^ 2)) ^ 2 = 1 := by
    field_simp
    ring
  have hg2 : 2 * u / (1 + u ^ 2) ≤ 2 * u := by
    rw [div_le_iff₀ hd]
    nlinarith
  have e : ((1 + h) ^ 2 + (1 + h)) * (2 * u) ≤ 1 := by
    have e1 : 1 - ((1 + h) ^ 2 + (1 + h)) * (2 * u) = h / (2 * (1 + h)) := by
      rw [hu]
      field_simp
      ring
    have e2 : 0 ≤ h / (2 * (1 + h)) := by positivity
    linarith
  have ht : ((1 + h) ^ 2 + (1 + h)) * (2 * u / (1 + u ^ 2)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hg2 (by positivity)).trans e
  have h3 : (1 + h) ^ 2 < ((1 - u ^ 2) / (1 + u ^ 2)
      + h * ((1 + (1 - u ^ 2) / (1 + u ^ 2)) / 2)) ^ 2 + ((1 + h) * (2 * u / (1 + u ^ 2))) ^ 2 := by
    obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = (1 - u ^ 2) / (1 + u ^ 2) := ⟨_, rfl⟩
    obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = 2 * u / (1 + u ^ 2) := ⟨_, rfl⟩
    rw [← hcd, ← hgd] at hcg
    rw [← hcd] at hc hc1
    rw [← hcd, ← hgd]
    have e1 : ((1 + h) * c) ^ 2 + ((1 + h) * g) ^ 2 = (1 + h) ^ 2 := by
      linear_combination (1 + h) ^ 2 * hcg
    have e2 : 0 < (c + h * ((1 + c) / 2) - (1 + h) * c) * (c + h * ((1 + c) / 2) + (1 + h) * c) :=
      mul_pos (by nlinarith) (by nlinarith)
    nlinarith
  obtain ⟨F, X, Y, Yh, h0, hX, hYh, hY, hr, hrk⟩ :=
    exists_plain_rank_gt_epsRank_of_params (κ := (1 + (1 - u ^ 2) / (1 + u ^ 2)) / 2) hh hc
      (by linarith) hg0 hg hcg.le ht h3
  exact ⟨_, F, X, Y, Yh, by linarith, by linarith, h0, hX, hYh, hY, hr, hrk⟩

/-- The hypotheses of `exists_plain_rank_gt_epsRank_of_params` hold with strict inequalities:
`h = 1/4`, `c = 93/100`, `g = 7/20`, `κ = 99/100`. In this instance no norm or entry of the
run equals the tolerance (the removed parts have norms `63/64` and `√0.9874`, the third step
has norm `> 1.004`), and `‖X₃‖ = 0.99 θ h / (1 + h)`. -/
example : ∃ (F : Matrix (Fin 2) (Fin 2) ℝ) (X Y Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
    X 0 = Y 0 ∧
    (∀ j < 3, X (j + 1) + (1 / 4 : ℝ) • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * X (j + 1) + X (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      = X j + (1 / 4 : ℝ) • F) ∧
    (∀ j < 3, Yh (j + 1) + (1 / 4 : ℝ) • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * Yh (j + 1) + Yh (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      = Y j + (1 / 4 : ℝ) • F) ∧
    (∀ j < 3, Y (j + 1) = truncation (Yh (j + 1)) (epsRank 1 (Yh (j + 1)))) ∧
    epsRank ((99 / 100 : ℝ) * ((1 / 4 : ℝ) / (1 + 1 / 4))) (X 3) = 0 ∧ (Y 3).rank = 1 :=
  exists_plain_rank_gt_epsRank_of_params (h := 1 / 4) (c := 93 / 100) (g := 7 / 20)
    (κ := 99 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end DecoupledCounterexample

/-! ### A start and a forcing without a common singular basis: rank two against rank one -/

section RotatedCounterexample

/-- **At `h = 1/9` no fraction of the tolerance repairs the comparison.** With `P = Q = 1/2`,
`h = 1/9` and the tolerance `θ = 1` there is a `2 × 2` problem for which the truncated backward
Euler run has rank two in the third step while the untruncated run has rank at most one there.
Hence `rank Y₃ > rank_δ(X₃)` for every `δ ≥ 0`. `P` and `Q` commute with everything; the start
`X₀` and the forcing `F` have no common singular basis. In the first step the singular value
`95/108` is removed along singular vectors rotated by `3-4-5` triangles (the kept one is `6`),
in the second step the singular value `9/10` along the coordinate axes (the kept one is
`15/2`); `Ŷ₃` has both singular values above `6/5`. No singular value or tail of the run
equals the tolerance. -/
theorem exists_plain_rank_gt_rank :
    ∃ (F : Matrix (Fin 2) (Fin 2) ℝ) (X Y Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      X 0 = Y 0 ∧
      (∀ j < 3, X (j + 1) + (1 / 9 : ℝ) • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        * X (j + 1) + X (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        = X j + (1 / 9 : ℝ) • F) ∧
      (∀ j < 3, Yh (j + 1) + (1 / 9 : ℝ) • (((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        * Yh (j + 1) + Yh (j + 1) * ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
        = Y j + (1 / 9 : ℝ) • F) ∧
      (∀ j < 3, Y (j + 1) = truncation (Yh (j + 1)) (epsRank 1 (Yh (j + 1)))) ∧
      (X 3).rank ≤ 1 ∧ (Y 3).rank = 2 := by
  obtain ⟨U, hUd⟩ : ∃ U : Matrix (Fin 2) (Fin 2) ℝ, U = !![3 / 5, -(4 / 5); 4 / 5, 3 / 5] :=
    ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : Matrix (Fin 2) (Fin 2) ℝ, V = !![-(4 / 5), -(3 / 5); 3 / 5, -(4 / 5)] :=
    ⟨_, rfl⟩
  have hU : Uᵀ * U = 1 := by
    rw [hUd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hV : Vᵀ * V = 1 := by
    rw [hVd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  obtain ⟨A, hAd⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
      A = U * diagonal ![6, -(95 / 108)] * Vᵀ := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : Matrix (Fin 2) (Fin 2) ℝ, T = U * diagonal ![6, 0] * Vᵀ := ⟨_, rfl⟩
  have hA : A = !![-(743 / 225), 1078 / 675; -(1057 / 300), 743 / 225] := by
    rw [hAd, hUd, hVd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;> norm_num
  have hT : T = !![-(72 / 25), 54 / 25; -(96 / 25), 72 / 25] := by
    rw [hTd, hUd, hVd]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;> norm_num
  obtain ⟨Gm, hGm⟩ : ∃ Gm : Matrix (Fin 2) (Fin 2) ℝ,
      Gm = !![2523 / 250, -(243 / 125); 432 / 125, -(423 / 250)] := ⟨_, rfl⟩
  have hY2 : (9 / 10 : ℝ) • T + Gm = diagonal ![15 / 2, 9 / 10] := by
    rw [hT, hGm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  obtain ⟨W, hWd⟩ : ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
      W = (9 / 10 : ℝ) • (diagonal ![15 / 2, 0] : Matrix (Fin 2) (Fin 2) ℝ) + Gm := ⟨_, rfl⟩
  have hW : W = !![8421 / 500, -(243 / 125); 432 / 125, -(423 / 250)] := by
    rw [hWd, hGm]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  have hX3 : (9 / 10 : ℝ) • ((9 / 10 : ℝ) • A + Gm) + Gm
      = vecMulVec ![1, 9 / 40] ![33 / 2, -(12 / 5)] := by
    rw [hA, hGm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply] <;> norm_num
  have hE1 : epsRank 1 A = 1 := by
    rw [hAd]
    refine epsRank_mul_diagonal_mul_transpose hU hV ?_ ?_
    · rw [abs_neg, abs_of_pos (by norm_num)]
      norm_num
    · norm_num
  have hT1 : truncation A 1 = T := by
    rw [hAd, hTd]
    refine truncation_one_mul_diagonal_mul_transpose hU hV ?_
    rw [abs_neg, abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
    norm_num
  have hE2 : epsRank 1 (diagonal ![15 / 2, 9 / 10] : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    epsRank_diagonal_two (by rw [abs_of_pos (by norm_num)]; norm_num) (by norm_num)
  have hT2 : truncation (diagonal ![15 / 2, 9 / 10] : Matrix (Fin 2) (Fin 2) ℝ) 1
      = diagonal ![15 / 2, 0] := by
    have h := truncation_one_mul_diagonal_mul_transpose (U := 1) (V := 1) (a := 15 / 2)
      (b := 9 / 10) (by simp) (by simp)
      (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num)
    simpa using h
  have hE3 : epsRank 1 W = 2 := by
    have hlow : (6 / 5 : ℝ) ≤ distLR 1 W := by
      rw [hW]
      refine le_distLR_of_le_mulVec (by simp) (by norm_num) fun x => ?_
      simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [sq_nonneg (73539225 * x 0 - 9647100 * x 1), sq_nonneg (x 1)]
    have hup : epsRank 1 W ≤ 2 :=
      (epsRank_le_rank zero_le_one).trans ((Matrix.rank_le_card_width _).trans (by simp))
    have hlt : ¬ epsRank 1 W ≤ 1 := fun hle => by
      have := (epsRank_le_iff zero_le_one).mp hle
      linarith
    omega
  obtain ⟨X, hX0, hX1, hX2, hX3'⟩ : ∃ X : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      X 0 = (10 / 9 : ℝ) • (A - Gm) ∧ X 1 = A ∧ X 2 = (9 / 10 : ℝ) • A + Gm ∧
      X 3 = (9 / 10 : ℝ) • ((9 / 10 : ℝ) • A + Gm) + Gm :=
    ⟨fun j => if j = 0 then (10 / 9 : ℝ) • (A - Gm) else if j = 1 then A
      else if j = 2 then (9 / 10 : ℝ) • A + Gm else (9 / 10 : ℝ) • ((9 / 10 : ℝ) • A + Gm) + Gm,
      by simp, by simp, by simp, by simp⟩
  obtain ⟨Y, hY0, hY1, hY2', hY3⟩ : ∃ Y : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      Y 0 = (10 / 9 : ℝ) • (A - Gm) ∧ Y 1 = T ∧ Y 2 = diagonal ![15 / 2, 0] ∧
      Y 3 = truncation W (epsRank 1 W) :=
    ⟨fun j => if j = 0 then (10 / 9 : ℝ) • (A - Gm) else if j = 1 then T
      else if j = 2 then diagonal ![15 / 2, 0] else truncation W (epsRank 1 W),
      by simp, by simp, by simp, by simp⟩
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ : ∃ Z : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
      Z 1 = A ∧ Z 2 = (9 / 10 : ℝ) • T + Gm ∧ Z 3 = W :=
    ⟨fun j => if j = 1 then A else if j = 2 then (9 / 10 : ℝ) • T + Gm else W,
      by simp, by simp, by simp⟩
  refine ⟨(10 : ℝ) • Gm, X, Y, Z, by rw [hX0, hY0], ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    apply add_smul_half_sylvester
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hX0, hX1]
      module
    · rw [hX1, hX2]
      module
    · rw [hX2, hX3']
      module
  · intro j hj
    apply add_smul_half_sylvester
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hY0, hZ1]
      module
    · rw [hY1, hZ2]
      module
    · rw [hY2', hZ3, hWd]
      module
  · intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · rw [hY1, hZ1, hE1, hT1]
    · rw [hY2', hZ2, hY2, hE2, hT2]
    · rw [hY3, hZ3]
  · rw [hX3', hX3]
    exact rank_vecMulVec_le _ _
  · rw [hY3, DynamicRecompression.rank_truncation_epsRank zero_le_one, hE3]

end RotatedCounterexample

/-! ### Decoupled modes with a sign condition: the comparison holds with the full tolerance -/

section DecoupledRun

/-- One backward Euler step of a scalar mode: if the truncated value lies between zero and the
untruncated value, on the side of the forcing, so does the next step from it. -/
theorem between_zero_and_untruncated_of_step {D s x y x' y' : ℝ} (hD : 0 < D)
    (hx : D * x' = x + s) (hy : D * y' = y + s)
    (h : (0 ≤ s ∧ 0 ≤ y ∧ y ≤ x) ∨ (s ≤ 0 ∧ x ≤ y ∧ y ≤ 0)) :
    (0 ≤ s ∧ 0 ≤ y' ∧ y' ≤ x') ∨ (s ≤ 0 ∧ x' ≤ y' ∧ y' ≤ 0) := by
  rcases h with ⟨hs, hy0, hyx⟩ | ⟨hs, hxy, hy0⟩
  · exact Or.inl ⟨hs, le_of_mul_le_mul_left (by rw [mul_zero, hy]; linarith) hD,
      le_of_mul_le_mul_left (by rw [hy, hx]; linarith) hD⟩
  · exact Or.inr ⟨hs, le_of_mul_le_mul_left (by rw [hy, hx]; linarith) hD,
      le_of_mul_le_mul_left (by rw [mul_zero, hy]; linarith) hD⟩

variable {ι : Type*} {p q f : ι → ℝ} {h : ℝ} {N : ℕ} {x y yh : ℕ → ι → ℝ}

/-- **Decoupled modes.** Mode `i` of the untruncated run `x`, of the step `yh` from the
truncated run, and of the truncated run `y` (which keeps or removes each mode). If every mode
starts between zero and the untruncated run on the side of its forcing, every mode of every
step from the truncated run is dominated by the untruncated run. -/
theorem abs_le_abs_of_decoupled_run (hh : 0 ≤ h) (hpq : ∀ i, 0 ≤ p i + q i)
    (hx : ∀ j < N, ∀ i, (1 + h * (p i + q i)) * x (j + 1) i = x j i + h * f i)
    (hyh : ∀ j < N, ∀ i, (1 + h * (p i + q i)) * yh (j + 1) i = y j i + h * f i)
    (hy : ∀ j < N, ∀ i, y (j + 1) i = yh (j + 1) i ∨ y (j + 1) i = 0)
    (h0 : ∀ i, (0 ≤ f i ∧ 0 ≤ y 0 i ∧ y 0 i ≤ x 0 i) ∨ (f i ≤ 0 ∧ x 0 i ≤ y 0 i ∧ y 0 i ≤ 0)) :
    ∀ j < N, ∀ i, |yh (j + 1) i| ≤ |x (j + 1) i| := by
  have hD : ∀ i, 0 < 1 + h * (p i + q i) := fun i =>
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hh (hpq i))
  have inv : ∀ j, j ≤ N → ∀ i, (0 ≤ h * f i ∧ 0 ≤ y j i ∧ y j i ≤ x j i) ∨
      (h * f i ≤ 0 ∧ x j i ≤ y j i ∧ y j i ≤ 0) := by
    intro j
    induction j with
    | zero =>
      intro _ i
      rcases h0 i with ⟨hf, h1, h2⟩ | ⟨hf, h1, h2⟩
      · exact Or.inl ⟨mul_nonneg hh hf, h1, h2⟩
      · exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos hh hf, h1, h2⟩
    | succ j ih =>
      intro hj i
      have hjN : j < N := hj
      rcases between_zero_and_untruncated_of_step (hD i) (hx j hjN i) (hyh j hjN i)
        (ih hjN.le i) with ⟨hs, h1, h2⟩ | ⟨hs, h1, h2⟩
      · refine Or.inl ⟨hs, ?_, ?_⟩ <;> rcases hy j hjN i with e | e <;> rw [e] <;> linarith
      · refine Or.inr ⟨hs, ?_, ?_⟩ <;> rcases hy j hjN i with e | e <;> rw [e] <;> linarith
  intro j hj i
  rcases between_zero_and_untruncated_of_step (hD i) (hx j hj i) (hyh j hj i)
    (inv j hj.le i) with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

/-- The hypotheses of `abs_le_abs_of_decoupled_run` can hold over two steps with a mode that is
removed and re-enters: `p = q = 1/2`, `h = 1`, forcing `(4, 1)`, start at zero. The untruncated
run is `(2, 1/2)`, `(3, 3/4)`; the truncated run removes the second mode in both steps, so the
second step from it is `(3, 1/2)` and differs from the untruncated run. -/
example : ∃ (p q f : Fin 2 → ℝ) (x y yh : ℕ → Fin 2 → ℝ), (∀ i, 0 ≤ p i + q i) ∧
    (∀ j < 2, ∀ i, (1 + 1 * (p i + q i)) * x (j + 1) i = x j i + 1 * f i) ∧
    (∀ j < 2, ∀ i, (1 + 1 * (p i + q i)) * yh (j + 1) i = y j i + 1 * f i) ∧
    (∀ j < 2, ∀ i, y (j + 1) i = yh (j + 1) i ∨ y (j + 1) i = 0) ∧
    (∀ i, (0 ≤ f i ∧ 0 ≤ y 0 i ∧ y 0 i ≤ x 0 i) ∨ (f i ≤ 0 ∧ x 0 i ≤ y 0 i ∧ y 0 i ≤ 0)) ∧
    y 1 ≠ yh 1 ∧ yh 2 ≠ x 2 := by
  refine ⟨fun _ => 1 / 2, fun _ => 1 / 2, ![4, 1],
    fun j => if j = 0 then 0 else if j = 1 then ![2, 1 / 2] else ![3, 3 / 4],
    fun j => if j = 0 then 0 else if j = 1 then ![2, 0] else ![3, 0],
    fun j => if j = 1 then ![2, 1 / 2] else ![3, 1 / 2], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    norm_num
  · intro j hj i
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
  · intro j hj i
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
  · intro j hj i
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · fin_cases i <;> simp
    · fin_cases i <;> simp
  · intro i
    left
    fin_cases i <;> simp
  · intro hne
    have := congrFun hne 1
    norm_num at this
  · intro hne
    have := congrFun hne 1
    norm_num at this

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal entries of a backward Euler step of the Sylvester equation with diagonal
data. -/
theorem diagonal_sylvester_apply {p q d e f : n → ℝ} {h : ℝ}
    (hd : diagonal d + h • (diagonal p * diagonal d + diagonal d * diagonal q)
      = diagonal e + h • diagonal f) (i : n) :
    (1 + h * (p i + q i)) * d i = e i + h * f i := by
  have h1 := congrFun (congrFun hd i) i
  simp only [Matrix.diagonal_mul_diagonal, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_apply_eq, smul_eq_mul] at h1
  linear_combination h1

/-- **Rank of the truncated run for decoupled modes.** Let `P = diag p`, `Q = diag q`,
`F = diag f` with `p i + q i ≥ 0`, let `X_j = diag (x j)` be the backward Euler run and
`Ŷ_{j+1} = diag (yh (j+1))` the step from `Y_j = diag (y j)`, where `Y_{j+1}` keeps or removes
each diagonal entry of `Ŷ_{j+1}` and has at most the tolerance rank of `Ŷ_{j+1}` (both are
hypotheses, `hy` and `hrank`; on ties the truncated singular value decomposition of a diagonal
matrix need not be diagonal). If every mode starts between zero and the untruncated run on the
side of its forcing (for instance `X_0 = Y_0 = 0`), then `rank Y_j ≤ rank_θ(X_j)` for all
steps, with the full tolerance. -/
theorem rank_le_epsRank_of_decoupled_run {p q f : n → ℝ} {h θ : ℝ} {N : ℕ}
    {x y yh : ℕ → n → ℝ} (hh : 0 ≤ h) (hpq : ∀ i, 0 ≤ p i + q i) (hθ : 0 ≤ θ)
    (hX : ∀ j < N, diagonal (x (j + 1)) + h • (diagonal p * diagonal (x (j + 1))
      + diagonal (x (j + 1)) * diagonal q) = diagonal (x j) + h • diagonal f)
    (hYh : ∀ j < N, diagonal (yh (j + 1)) + h • (diagonal p * diagonal (yh (j + 1))
      + diagonal (yh (j + 1)) * diagonal q) = diagonal (y j) + h • diagonal f)
    (hy : ∀ j < N, ∀ i, y (j + 1) i = yh (j + 1) i ∨ y (j + 1) i = 0)
    (hrank : ∀ j < N, (diagonal (y (j + 1)) : Matrix n n ℝ).rank
      ≤ epsRank θ (diagonal (yh (j + 1)) : Matrix n n ℝ))
    (h0 : ∀ i, (0 ≤ f i ∧ 0 ≤ y 0 i ∧ y 0 i ≤ x 0 i) ∨ (f i ≤ 0 ∧ x 0 i ≤ y 0 i ∧ y 0 i ≤ 0)) :
    ∀ j < N, (diagonal (y (j + 1)) : Matrix n n ℝ).rank
      ≤ epsRank θ (diagonal (x (j + 1)) : Matrix n n ℝ) := fun j hj =>
  (hrank j hj).trans (epsRank_diagonal_le_of_abs_le
    (abs_le_abs_of_decoupled_run hh hpq (fun j hj i => diagonal_sylvester_apply (hX j hj) i)
      (fun j hj i => diagonal_sylvester_apply (hYh j hj) i) hy h0 j hj) hθ)

/-- The hypotheses of `rank_le_epsRank_of_decoupled_run` can hold over two steps with a mode
that is removed and re-enters: `p = q = 1/2`, `h = 1`, `θ = 1`, forcing `(4, 1)`, start at
zero. The untruncated run is `diag(2, 1/2)`, `diag(3, 3/4)`; the truncated run removes the
second entry in both steps, and the second step from it is `diag(3, 1/2) ≠ X₂`. -/
example : ∃ (x y yh : ℕ → Fin 2 → ℝ) (f : Fin 2 → ℝ),
    (∀ j < 2, diagonal (x (j + 1)) + (1 : ℝ) • (diagonal (fun _ => (1 / 2 : ℝ))
      * diagonal (x (j + 1)) + diagonal (x (j + 1)) * diagonal (fun _ => (1 / 2 : ℝ)))
      = diagonal (x j) + (1 : ℝ) • diagonal f) ∧
    (∀ j < 2, diagonal (yh (j + 1)) + (1 : ℝ) • (diagonal (fun _ => (1 / 2 : ℝ))
      * diagonal (yh (j + 1)) + diagonal (yh (j + 1)) * diagonal (fun _ => (1 / 2 : ℝ)))
      = diagonal (y j) + (1 : ℝ) • diagonal f) ∧
    (∀ j < 2, ∀ i, y (j + 1) i = yh (j + 1) i ∨ y (j + 1) i = 0) ∧
    (∀ j < 2, (diagonal (y (j + 1)) : Matrix (Fin 2) (Fin 2) ℝ).rank
      ≤ epsRank 1 (diagonal (yh (j + 1)) : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ i, (0 ≤ f i ∧ 0 ≤ y 0 i ∧ y 0 i ≤ x 0 i) ∨ (f i ≤ 0 ∧ x 0 i ≤ y 0 i ∧ y 0 i ≤ 0)) ∧
    y 1 ≠ yh 1 ∧ yh 2 ≠ x 2 := by
  have key : ∀ d e : Fin 2 → ℝ, (∀ i, 2 * d i = e i + ![4, 1] i) →
      diagonal d + (1 : ℝ) • (diagonal (fun _ => (1 / 2 : ℝ)) * diagonal d
        + diagonal d * diagonal (fun _ => (1 / 2 : ℝ)))
        = diagonal e + (1 : ℝ) • diagonal ![4, 1] := by
    intro d e hde
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_mul_diagonal, Matrix.add_apply, Matrix.smul_apply,
        Matrix.diagonal_apply_eq, smul_eq_mul]
      linarith [hde i]
    · simp [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij]
  have hE : ∀ a : ℝ, 1 < a → epsRank 1 (diagonal ![a, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
    fun a ha => epsRank_diagonal_two (by rw [abs_of_pos (by norm_num)]; norm_num) (by nlinarith)
  refine ⟨fun j => if j = 0 then 0 else if j = 1 then ![2, 1 / 2] else ![3, 3 / 4],
    fun j => if j = 0 then 0 else if j = 1 then ![2, 0] else ![3, 0],
    fun j => if j = 1 then ![2, 1 / 2] else ![3, 1 / 2], ![4, 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact key _ _ fun i => by fin_cases i <;> norm_num
    · exact key _ _ fun i => by fin_cases i <;> norm_num
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact key _ _ fun i => by fin_cases i <;> norm_num
    · exact key _ _ fun i => by fin_cases i <;> norm_num
  · intro j hj i
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · fin_cases i <;> simp
    · fin_cases i <;> simp
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · change (diagonal ![2, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank
        ≤ epsRank 1 (diagonal ![2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)
      rw [hE 2 (by norm_num)]
      exact rank_diagonal_two_le_one 2
    · change (diagonal ![3, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank
        ≤ epsRank 1 (diagonal ![3, 1 / 2] : Matrix (Fin 2) (Fin 2) ℝ)
      rw [hE 3 (by norm_num)]
      exact rank_diagonal_two_le_one 3
  · intro i
    left
    fin_cases i <;> simp
  · intro hne
    have := congrFun hne 1
    norm_num at this
  · intro hne
    have := congrFun hne 1
    norm_num at this

end DecoupledRun

end LeanDLRA.PlainTruncationRank

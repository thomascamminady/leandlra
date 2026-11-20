import LeanDLRA.Research.InformationLowerBound

/-!
# The two-field lower bound for low-rank information in every dimension and rank

`LeanDLRA/Research/InformationLowerBound.lean` shows that a method which uses the field `F` only
through its values on `M_{≤ k}` (the matrices of rank at most `k`) has error at least
`L ∫₀ᵀ dist(A(s), M_{≤ k}) ds` for one of two `L`-Lipschitz fields, with an explicit pair of
`2 × 2` fields and `k = 1`. This file gives the pair for all sizes `m × n` and all ranks `k ≥ 1`
with `k + 1 ≤ m`, `k + 1 ≤ n`, by embedding the diagonal construction of size `k + 1` with two
matrices `U`, `V` of `k + 1` orthonormal columns: with `W = u₁ v₁ᵀ`, `B = u_{k+1} v_{k+1}ᵀ`,

    F_c(t, Z) = B + c dist(Z, M_{≤ k}) W,   A_c(t) = U diag(a + c t²/2, a, …, a, t) Vᵀ,

the curve `A_c` solves `y' = F_c(t, y)` from the start `A_c(0)` of rank at most `k`, as long as
`T + |c| T²/2 ≤ a`, with `dist(A_c(t), M_{≤ k}) = t` and

    ‖A_L(T) - A_{-L}(T)‖ = L T² = 2 L ∫₀ᵀ dist(A_{±L}(s), M_{≤ k}) ds.

The second part is the dissipative version: with `G(Z) = μ A₀ + B - μ Z` and
`F_± = G ± L dist(·, M_{≤ k}) W`, `0 ≤ L`, `0 < μ`, the fields are one-sided Lipschitz with the
constant `L - μ` (dissipative for `L ≤ μ`), agree on `M_{≤ k}`, and the exact solutions
`A_±(t) = A₀ + y(t) B ± z(t) W`, `y(t) = (1 - e^{-μ t})/μ`,
`z(t) = L (1 - e^{-μ t} - μ t e^{-μ t})/μ²` give

    ‖A₊(T) - A₋(T)‖ / 2 = L ∫₀ᵀ e^{-μ (T - s)} dist(A(s), M_{≤ k}) ds ≤ (L/μ) dist(A(T), M_{≤ k}).

For this pair the forced error is at most `L/μ` times the best approximation error at the final
time; it is not of the size `L ∫ dist`. The weight `e^{-μ (T - s)}` is not the weight
`e^{ℓ (T - s)}`, `ℓ = L - μ`, of the usual upper bounds for one-sided Lipschitz fields (the two
differ by the factor `e^{L (T - s)}`), so this lower bound is not shown to match an upper bound.

## Main results

* `InformationLowerBoundGeneral.le_distLR_mul_diagonal_mul_transpose`: the distance of
  `U diag(d) Vᵀ` to `M_{≤ r}` is at least `min |dᵢ|` when `r` is below the number of columns.
* `InformationLowerBoundGeneralExample.distLR_frameSol`, `odeSolution_frameSol`,
  `norm_frameSol_sub_eq_two_mul_integral`, `mul_integral_distLR_le_max_error`: the pair.
* `InformationLowerBoundGeneral.exists_lowRank_information_pair`: the pair exists for every size
  `m × n` and every rank `1 ≤ k` with `k + 1 ≤ m`, `k + 1 ≤ n`.
* `InformationLowerBoundGeneralExample.odeSolution_dissSol`,
  `norm_dissSol_sub_eq_two_mul_integral`, `mul_integral_exp_distLR_le_max_error`,
  `mul_integral_exp_distLR_dissSol_le`, `dissZ_pos`: the dissipative pair.
-/

open Set MeasureTheory
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.InformationLowerBoundGeneral

section Frames

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq ι]
  {U : Matrix m ι ℝ} {V : Matrix n ι ℝ}

/-- With orthonormal columns in `U` and `V`, `‖U M Vᵀ‖ = ‖M‖`. -/
theorem norm_mul_mul_transpose_of_orthonormal (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (M : Matrix ι ι ℝ) : ‖U * M * Vᵀ‖ = ‖M‖ := by
  rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU,
    Frobenius.norm_mul_transpose_of_orthonormal hV]

/-- **Distance of an embedded diagonal matrix.** If `U`, `V` have orthonormal columns,
`|dᵢ| ≥ c ≥ 0` for all `i` and `r` is less than the number of columns, then
`dist(U diag(d) Vᵀ, M_{≤ r}) ≥ c`. The compression `X ↦ Uᵀ X V` does not raise the norm or the
rank and maps `U diag(d) Vᵀ` to `diag(d)`. -/
theorem le_distLR_mul_diagonal_mul_transpose (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {d : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, c ≤ |d i|) {r : ℕ}
    (hr : r < Fintype.card ι) :
    c ≤ distLR r (U * Matrix.diagonal d * Vᵀ) := by
  rw [le_distLR_iff]
  intro Z hZ
  have h1 : c ≤ distLR r (Matrix.diagonal d) := le_distLR_diagonal hc hd hr
  have hZ' : (Uᵀ * Z * V).rank ≤ r :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hZ)
  have h2 : distLR r (Matrix.diagonal d) ≤ ‖Matrix.diagonal d - Uᵀ * Z * V‖ :=
    distLR_le_norm_sub hZ'
  have hD : Uᵀ * (U * Matrix.diagonal d * Vᵀ) * V = Matrix.diagonal d := by
    rw [show Uᵀ * (U * Matrix.diagonal d * Vᵀ) * V = (Uᵀ * U) * Matrix.diagonal d * (Vᵀ * V) by
      simp only [Matrix.mul_assoc], hU, hV, Matrix.one_mul, Matrix.mul_one]
  have e : Matrix.diagonal d - Uᵀ * Z * V = Uᵀ * (U * Matrix.diagonal d * Vᵀ - Z) * V := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hD]
  have h3 : ‖Uᵀ * (U * Matrix.diagonal d * Vᵀ - Z) * V‖ ≤ ‖U * Matrix.diagonal d * Vᵀ - Z‖ :=
    (norm_mul_le_of_orthonormal hV _).trans (norm_transpose_mul_le hU _)
  rw [e] at h2
  linarith

omit [Fintype m] in
/-- An embedded diagonal matrix with a zero entry has rank less than the number of columns. -/
theorem rank_mul_diagonal_mul_transpose_lt (U : Matrix m ι ℝ) (V : Matrix n ι ℝ) {d : ι → ℝ}
    {i : ι} (hi : d i = 0) : (U * Matrix.diagonal d * Vᵀ).rank < Fintype.card ι := by
  classical
  calc (U * Matrix.diagonal d * Vᵀ).rank ≤ (Matrix.diagonal d).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    _ = Fintype.card {j // d j ≠ 0} := Matrix.rank_diagonal d
    _ < Fintype.card ι := Fintype.card_subtype_lt (x := i) (by simp [hi])

/-- The Frobenius norm of a diagonal matrix with one entry `1` and zeros elsewhere is `1`. -/
theorem norm_diagonal_ite_eq (j : ι) :
    ‖(Matrix.diagonal fun i => if i = j then (1 : ℝ) else 0)‖ = 1 := by
  rw [Frobenius.norm_def]
  have h : ∑ i, ∑ l, (Matrix.diagonal (fun i => if i = j then (1 : ℝ) else 0)) i l ^ 2 = 1 := by
    simp [Matrix.diagonal_apply]
  rw [h, Real.sqrt_one]

end Frames

end LeanDLRA.InformationLowerBoundGeneral

/-! ### The pair of fields -/

namespace LeanDLRA.InformationLowerBoundGeneralExample

open LeanDLRA.InformationLowerBound LeanDLRA.InformationLowerBoundGeneral

variable {m n : Type*} {k : ℕ}

/-- The direction `B = u_{k+1} v_{k+1}ᵀ` of the common field. -/
noncomputable def frameB (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ) :
    Matrix m n ℝ :=
  U * Matrix.diagonal (fun i => if i = Fin.last k then (1 : ℝ) else 0) * Vᵀ

/-- The direction `W = u₁ v₁ᵀ` of the perturbation. -/
noncomputable def frameW (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ) :
    Matrix m n ℝ :=
  U * Matrix.diagonal (fun i : Fin (k + 1) => if i = 0 then (1 : ℝ) else 0) * Vᵀ

/-- The start `A₀ = a (u₁ v₁ᵀ + ⋯ + u_k v_kᵀ)`. -/
noncomputable def frameStart (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a : ℝ) : Matrix m n ℝ :=
  U * Matrix.diagonal (fun i => if i = Fin.last k then 0 else a) * Vᵀ

/-- The matrix `A₀ + s W + y B = U diag(a + s, a, …, a, y) Vᵀ`. -/
noncomputable def frameCurve (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a s y : ℝ) : Matrix m n ℝ :=
  frameStart U V a + s • frameW U V + y • frameB U V

/-- The curve `A_c(t) = A₀ + (c t²/2) W + t B`. -/
noncomputable def frameSol (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a c t : ℝ) : Matrix m n ℝ :=
  frameCurve U V a (c * t ^ 2 / 2) t

/-- The diagonal `(a + s, a, …, a, y)` of `frameCurve`. -/
noncomputable def frameDiag (k : ℕ) (a s y : ℝ) (i : Fin (k + 1)) : ℝ :=
  (if i = Fin.last k then 0 else a) + s * (if i = 0 then 1 else 0) +
    y * (if i = Fin.last k then 1 else 0)

lemma last_ne_zero (hk : 1 ≤ k) : Fin.last k ≠ 0 := fun h => by
  have h' := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at h'
  omega

lemma frameDiag_last (hk : 1 ≤ k) (a s y : ℝ) : frameDiag k a s y (Fin.last k) = y := by
  simp [frameDiag, last_ne_zero hk]

lemma frameDiag_zero (hk : 1 ≤ k) (a s y : ℝ) : frameDiag k a s y 0 = a + s := by
  simp [frameDiag, (last_ne_zero hk).symm]

lemma frameDiag_of_ne {a s y : ℝ} {i : Fin (k + 1)} (hl : i ≠ Fin.last k) (h0 : i ≠ 0) :
    frameDiag k a s y i = a := by
  simp [frameDiag, hl, h0]

/-- `U diag(d₁) Vᵀ + s U diag(d₂) Vᵀ = U diag(d₁ + s d₂) Vᵀ`. -/
lemma frame_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix m ι ℝ)
    (V : Matrix n ι ℝ) (d₁ d₂ : ι → ℝ) (s : ℝ) :
    U * Matrix.diagonal d₁ * Vᵀ + s • (U * Matrix.diagonal d₂ * Vᵀ) =
      U * Matrix.diagonal (fun i => d₁ i + s * d₂ i) * Vᵀ := by
  have e : Matrix.diagonal (fun i => d₁ i + s * d₂ i) =
      Matrix.diagonal d₁ + s • Matrix.diagonal d₂ := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h]
  rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem frameCurve_eq (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a s y : ℝ) : frameCurve U V a s y = U * Matrix.diagonal (frameDiag k a s y) * Vᵀ := by
  rw [frameCurve, frameStart, frameW, frameB, frame_add_smul, frame_add_smul]
  rfl

/-- The start `A_c(0) = A₀` does not depend on `c`. -/
theorem frameSol_zero (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a c : ℝ) : frameSol U V a c 0 = frameStart U V a := by
  simp [frameSol, frameCurve]

/-- `A₀ + s W` has rank at most `k`. -/
theorem rank_frameStart_add_smul_le [Fintype n] (hk : 1 ≤ k) (U : Matrix m (Fin (k + 1)) ℝ)
    (V : Matrix n (Fin (k + 1)) ℝ) (a s : ℝ) : (frameStart U V a + s • frameW U V).rank ≤ k := by
  have e : frameStart U V a + s • frameW U V = U * Matrix.diagonal (fun i : Fin (k + 1) =>
      (if i = Fin.last k then 0 else a) + s * (if i = 0 then (1 : ℝ) else 0)) * Vᵀ := by
    rw [frameStart, frameW, frame_add_smul]
  have h := rank_mul_diagonal_mul_transpose_lt U V (i := Fin.last k)
    (d := fun i : Fin (k + 1) =>
      (if i = Fin.last k then 0 else a) + s * (if i = 0 then (1 : ℝ) else 0))
    (by simp [last_ne_zero hk])
  rw [← e, Fintype.card_fin] at h
  omega

theorem rank_frameSol_zero_le [Fintype n] (hk : 1 ≤ k) (U : Matrix m (Fin (k + 1)) ℝ)
    (V : Matrix n (Fin (k + 1)) ℝ) (a c : ℝ) : (frameSol U V a c 0).rank ≤ k := by
  have h := rank_frameStart_add_smul_le hk U V a 0
  rwa [zero_smul, add_zero, ← frameSol_zero U V a c] at h

variable [Fintype m] [Fintype n] {U : Matrix m (Fin (k + 1)) ℝ} {V : Matrix n (Fin (k + 1)) ℝ}

/-- The field `F_c(t, Z) = B + c dist(Z, M_{≤ k}) W`. -/
noncomputable def frameField (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (c : ℝ) (_ : ℝ) (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  frameB U V + (c * distLR k Z) • frameW U V

theorem norm_frameW (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) : ‖frameW U V‖ = 1 := by
  rw [frameW, norm_mul_mul_transpose_of_orthonormal hU hV, norm_diagonal_ite_eq]

theorem norm_frameB (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) : ‖frameB U V‖ = 1 := by
  rw [frameB, norm_mul_mul_transpose_of_orthonormal hU hV, norm_diagonal_ite_eq]

/-- **The distance of the curve.** If `0 ≤ y ≤ a` and `y ≤ a + s`, then
`dist(A₀ + s W + y B, M_{≤ k}) = y`. -/
theorem distLR_frameCurve (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a s y : ℝ}
    (hy : 0 ≤ y) (ha : y ≤ a) (hs : y ≤ a + s) : distLR k (frameCurve U V a s y) = y := by
  refine le_antisymm ?_ ?_
  · refine (distLR_le_norm_sub (rank_frameStart_add_smul_le hk U V a s)).trans (le_of_eq ?_)
    have e : frameCurve U V a s y - (frameStart U V a + s • frameW U V) = y • frameB U V := by
      rw [frameCurve]; abel
    rw [e, norm_smul, norm_frameB hU hV, mul_one, Real.norm_of_nonneg hy]
  · rw [frameCurve_eq]
    refine le_distLR_mul_diagonal_mul_transpose hU hV hy (fun i => ?_) (by simp)
    by_cases hl : i = Fin.last k
    · rw [hl, frameDiag_last hk, abs_of_nonneg hy]
    · by_cases h0 : i = 0
      · rw [h0, frameDiag_zero hk, abs_of_nonneg (by linarith)]
        exact hs
      · rw [frameDiag_of_ne hl h0, abs_of_nonneg (by linarith)]
        exact ha

/-- Along the curve of the pair the distance to `M_{≤ k}` is `t`, as long as
`T + |c| T² / 2 ≤ a`. -/
theorem distLR_frameSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a c t T : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ T) (hT : T + |c| * T ^ 2 / 2 ≤ a) :
    distLR k (frameSol U V a c t) = t := by
  have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h2 : 0 ≤ (c + |c|) * t ^ 2 := mul_nonneg (by linarith [neg_abs_le c]) (sq_nonneg t)
  have h3 : 0 ≤ |c| * (T ^ 2 - t ^ 2) := mul_nonneg (abs_nonneg c) (sub_nonneg.2 hsq)
  have h4 : 0 ≤ |c| * T ^ 2 := mul_nonneg (abs_nonneg c) (sq_nonneg T)
  exact distLR_frameCurve hk hU hV h0 (by linarith) (by nlinarith)

/-- Both fields equal `B` on `M_{≤ k}`. -/
theorem frameField_of_rank_le (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (c t : ℝ) {Z : Matrix m n ℝ} (hZ : Z.rank ≤ k) : frameField U V c t Z = frameB U V :=
  add_distLR_smul_of_rank_le (fun _ _ => frameB U V) (frameW U V) c t hZ

/-- The field `F_c` is Lipschitz with the constant `|c|`. -/
theorem isLipschitzField_frameField (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (c : ℝ) :
    IsLipschitzField (frameField U V c) |c| := by
  have h := isLipschitzField_add_distLR_smul (G := fun _ _ => frameB U V) (L₀ := 0)
    (fun t X Y => by simp) (frameW U V) c k
  rwa [norm_frameW hU hV, mul_one, zero_add] at h

theorem hasDerivAt_frameSol (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a c t : ℝ) : HasDerivAt (frameSol U V a c) (frameB U V + (c * t) • frameW U V) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s ^ 2 / 2) (c * t) t := by
    have h := ((hasDerivAt_pow 2 t).const_mul c).div_const 2
    refine h.congr_deriv ?_
    norm_num
    ring
  have h2 := ((h1.smul_const (frameW U V)).const_add (frameStart U V a)).add
    ((hasDerivAt_id' t).smul_const (frameB U V))
  rw [one_smul, add_comm ((c * t) • frameW U V) (frameB U V)] at h2
  exact h2

/-- **The exact solutions.** `A_c` solves `y' = F_c(t, y)` on `[0, T]` if
`T + |c| T² / 2 ≤ a`. -/
theorem odeSolution_frameSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a c T : ℝ}
    (hT : T + |c| * T ^ 2 / 2 ≤ a) : ODESolution (frameField U V c) (frameSol U V a c) 0 T where
  cont := fun t _ => (hasDerivAt_frameSol U V a c t).continuousAt.continuousWithinAt
  deriv t ht := by
    rw [frameField, distLR_frameSol hk hU hV ht.1 ht.2.le hT]
    exact (hasDerivAt_frameSol U V a c t).hasDerivWithinAt

/-- The two solutions differ by `L T² W` at the time `T`. -/
theorem norm_frameSol_sub_frameSol (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a T : ℝ) {L : ℝ}
    (hL : 0 ≤ L) : ‖frameSol U V a L T - frameSol U V a (-L) T‖ = L * T ^ 2 := by
  have e : frameSol U V a L T - frameSol U V a (-L) T = (L * T ^ 2) • frameW U V := by
    rw [show L * T ^ 2 = L * T ^ 2 / 2 - -L * T ^ 2 / 2 by ring, sub_smul, frameSol, frameSol,
      frameCurve, frameCurve]
    abel
  rw [e, norm_smul, norm_frameW hU hV, mul_one,
    Real.norm_of_nonneg (mul_nonneg hL (sq_nonneg T))]

theorem integral_distLR_frameSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a c T : ℝ}
    (h0 : 0 ≤ T) (hT : T + |c| * T ^ 2 / 2 ≤ a) :
    ∫ s in (0 : ℝ)..T, distLR k (frameSol U V a c s) = T ^ 2 / 2 := by
  have h : ∫ s in (0 : ℝ)..T, distLR k (frameSol U V a c s) = ∫ s in (0 : ℝ)..T, s :=
    intervalIntegral.integral_congr fun s hs => by
      rw [uIcc_of_le h0] at hs
      exact distLR_frameSol hk hU hV hs.1 hs.2 hT
  rw [h, integral_id]
  ring

/-- **The identity of the pair.** For `c = L` and for `c = -L`:
`‖A_L(T) - A_{-L}(T)‖ = 2 L ∫₀ᵀ dist(A_c(s), M_{≤ k}) ds`. -/
theorem norm_frameSol_sub_eq_two_mul_integral (hk : 1 ≤ k) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) {a L T c : ℝ} (hL : 0 ≤ L) (h0 : 0 ≤ T) (hT : T + L * T ^ 2 / 2 ≤ a)
    (hc : c = L ∨ c = -L) :
    ‖frameSol U V a L T - frameSol U V a (-L) T‖ =
      2 * L * ∫ s in (0 : ℝ)..T, distLR k (frameSol U V a c s) := by
  have hc' : |c| = L := by
    rcases hc with rfl | rfl
    · exact abs_of_nonneg hL
    · rw [abs_neg, abs_of_nonneg hL]
  rw [norm_frameSol_sub_frameSol hU hV a T hL,
    integral_distLR_frameSol hk hU hV h0 (by rwa [hc'])]
  ring

/-- **Lower bound for every method with rank-`k` information, any size.** Let the output `Φ F`
depend on `F` only through the values of `F` at matrices of rank at most `k`. For the two
`L`-Lipschitz fields `F_L`, `F_{-L}` (equal on `M_{≤ k}`, with the same start of rank at most `k`)
the error at the time `T` is at least `L ∫₀ᵀ dist(A(s), M_{≤ k}) ds` for one of them. -/
theorem mul_integral_distLR_le_max_error (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a L T c : ℝ} (hL : 0 ≤ L) (h0 : 0 ≤ T) (hT : T + L * T ^ 2 / 2 ≤ a) (hc : c = L ∨ c = -L)
    (Φ : (ℝ → Matrix m n ℝ → Matrix m n ℝ) → Matrix m n ℝ)
    (hΦ : ∀ F G : ℝ → Matrix m n ℝ → Matrix m n ℝ,
      (∀ t (Z : Matrix m n ℝ), Z.rank ≤ k → F t Z = G t Z) → Φ F = Φ G) :
    L * ∫ s in (0 : ℝ)..T, distLR k (frameSol U V a c s) ≤
      max ‖Φ (frameField U V L) - frameSol U V a L T‖
        ‖Φ (frameField U V (-L)) - frameSol U V a (-L) T‖ := by
  have h := half_norm_sub_le_max_error (S := {p : ℝ × Matrix m n ℝ | p.2.rank ≤ k}) Φ
    (fun F G hFG => hΦ F G fun t Z hZ => hFG (t, Z) hZ)
    (F₁ := frameField U V L) (F₂ := frameField U V (-L))
    (fun p hp => by
      rw [frameField_of_rank_le U V L p.1 hp, frameField_of_rank_le U V (-L) p.1 hp])
    (frameSol U V a L T) (frameSol U V a (-L) T)
  rw [norm_frameSol_sub_eq_two_mul_integral hk hU hV hL h0 hT hc] at h
  linarith

/-- For each field of the pair the output `A₀ + T B` has the error `|c| T² / 2`. -/
theorem norm_frameSol_sub_central (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a c T : ℝ) :
    ‖frameSol U V a c T - (frameSol U V a c 0 + T • frameB U V)‖ = |c| * T ^ 2 / 2 := by
  have e : frameSol U V a c T - (frameSol U V a c 0 + T • frameB U V) =
      (c * T ^ 2 / 2) • frameW U V := by
    rw [frameSol_zero, frameSol, frameCurve]
    abel
  rw [e, norm_smul, norm_frameW hU hV, mul_one, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg T), abs_two]

end LeanDLRA.InformationLowerBoundGeneralExample

namespace LeanDLRA.InformationLowerBoundGeneral

open LeanDLRA.InformationLowerBoundGeneralExample

/-- **The pair exists in every size and rank.** Let `1 ≤ k`, `k + 1 ≤ card m`, `k + 1 ≤ card n`,
`0 ≤ L`, `0 ≤ T` and `T + L T² / 2 ≤ a`. There are two `L`-Lipschitz fields `F₁`, `F₂` on
`m × n` matrices that agree on `M_{≤ k}`, and solutions `A₁`, `A₂` on `[0, T]` from the same
start of rank at most `k`, with `dist(A±(t), M_{≤ k}) = t` on `[0, T]`,
`‖A₁(T) - A₂(T)‖ = L T² = 2 L ∫₀ᵀ dist(A±(s), M_{≤ k}) ds`, such that every method whose output
depends on the field only through its values on `M_{≤ k}` has error at least
`L ∫₀ᵀ dist(A±(s), M_{≤ k}) ds` for one of the two fields. -/
theorem exists_lowRank_information_pair {m n : Type*} [Fintype m] [Fintype n] {k : ℕ}
    (hk : 1 ≤ k) (hm : k + 1 ≤ Fintype.card m) (hn : k + 1 ≤ Fintype.card n) {a L T : ℝ}
    (hL : 0 ≤ L) (h0 : 0 ≤ T) (hT : T + L * T ^ 2 / 2 ≤ a) :
    ∃ (F₁ F₂ : ℝ → Matrix m n ℝ → Matrix m n ℝ) (A₁ A₂ : ℝ → Matrix m n ℝ),
      IsLipschitzField F₁ L ∧ IsLipschitzField F₂ L ∧
      (∀ t (Z : Matrix m n ℝ), Z.rank ≤ k → F₁ t Z = F₂ t Z) ∧
      ODESolution F₁ A₁ 0 T ∧ ODESolution F₂ A₂ 0 T ∧ A₁ 0 = A₂ 0 ∧ (A₁ 0).rank ≤ k ∧
      (∀ t ∈ Icc (0 : ℝ) T, distLR k (A₁ t) = t ∧ distLR k (A₂ t) = t) ∧
      ‖A₁ T - A₂ T‖ = L * T ^ 2 ∧
      ‖A₁ T - A₂ T‖ = 2 * L * ∫ s in (0 : ℝ)..T, distLR k (A₁ s) ∧
      ‖A₁ T - A₂ T‖ = 2 * L * ∫ s in (0 : ℝ)..T, distLR k (A₂ s) ∧
      ∀ Φ : (ℝ → Matrix m n ℝ → Matrix m n ℝ) → Matrix m n ℝ,
        (∀ F G : ℝ → Matrix m n ℝ → Matrix m n ℝ,
          (∀ t (Z : Matrix m n ℝ), Z.rank ≤ k → F t Z = G t Z) → Φ F = Φ G) →
        L * ∫ s in (0 : ℝ)..T, distLR k (A₁ s) ≤ max ‖Φ F₁ - A₁ T‖ ‖Φ F₂ - A₂ T‖ := by
  obtain ⟨U, hU, -⟩ := exists_orthonormal_capture_of_le_card (0 : Matrix m (Fin (k + 1)) ℝ) hm
  obtain ⟨V, hV, -⟩ := exists_orthonormal_capture_of_le_card (0 : Matrix n (Fin (k + 1)) ℝ) hn
  have hLa : |L| = L := abs_of_nonneg hL
  have hLb : |-L| = L := by rw [abs_neg, hLa]
  refine ⟨frameField U V L, frameField U V (-L), frameSol U V a L, frameSol U V a (-L), ?_, ?_,
    fun t Z hZ => ?_, odeSolution_frameSol hk hU hV (by rwa [hLa]),
    odeSolution_frameSol hk hU hV (by rwa [hLb]), by rw [frameSol_zero, frameSol_zero],
    rank_frameSol_zero_le hk U V a L, fun t ht => ⟨distLR_frameSol hk hU hV ht.1 ht.2
      (by rwa [hLa]), distLR_frameSol hk hU hV ht.1 ht.2 (by rwa [hLb])⟩,
    norm_frameSol_sub_frameSol hU hV a T hL,
    norm_frameSol_sub_eq_two_mul_integral hk hU hV hL h0 hT (Or.inl rfl),
    norm_frameSol_sub_eq_two_mul_integral hk hU hV hL h0 hT (Or.inr rfl),
    fun Φ hΦ => mul_integral_distLR_le_max_error hk hU hV hL h0 hT (Or.inl rfl) Φ hΦ⟩
  · simpa [hLa] using isLipschitzField_frameField hU hV L
  · simpa [hLb] using isLipschitzField_frameField hU hV (-L)
  · rw [frameField_of_rank_le U V L t hZ, frameField_of_rank_le U V (-L) t hZ]

end LeanDLRA.InformationLowerBoundGeneral

/-! ### The dissipative pair -/

namespace LeanDLRA.InformationLowerBoundGeneralExample

open LeanDLRA.InformationLowerBound LeanDLRA.InformationLowerBoundGeneral

variable {m n : Type*} [Fintype m] [Fintype n] {k : ℕ}
  {U : Matrix m (Fin (k + 1)) ℝ} {V : Matrix n (Fin (k + 1)) ℝ}

/-- `y(t) = (1 - e^{-μ t}) / μ`, the distance of the dissipative solutions to `M_{≤ k}`. -/
noncomputable def dissY (μ t : ℝ) : ℝ := (1 - Real.exp (-μ * t)) / μ

/-- `z_c(t) = c (1 - e^{-μ t} - μ t e^{-μ t}) / μ²`. -/
noncomputable def dissZ (μ c t : ℝ) : ℝ :=
  c * (1 - Real.exp (-μ * t) - μ * t * Real.exp (-μ * t)) / μ ^ 2

/-- The field `F_c(t, Z) = μ A₀ + B - μ Z + c dist(Z, M_{≤ k}) W`. -/
noncomputable def dissField (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a μ c : ℝ) (_ : ℝ) (Z : Matrix m n ℝ) : Matrix m n ℝ :=
  (μ • frameStart U V a + frameB U V - μ • Z) + (c * distLR k Z) • frameW U V

/-- The curve `A_c(t) = A₀ + z_c(t) W + y(t) B`. -/
noncomputable def dissSol (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a μ c t : ℝ) : Matrix m n ℝ :=
  frameCurve U V a (dissZ μ c t) (dissY μ t)

lemma exp_neg_mul_mul_exp (μ t : ℝ) : Real.exp (-μ * t) * Real.exp (μ * t) = 1 := by
  rw [← Real.exp_add, show -μ * t + μ * t = 0 by ring, Real.exp_zero]

lemma dissY_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) : 0 ≤ dissY μ t := by
  have h : Real.exp (-μ * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  exact div_nonneg (by linarith) hμ.le

lemma dissY_le {μ : ℝ} (hμ : 0 < μ) (t : ℝ) : dissY μ t ≤ 1 / μ :=
  div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-μ * t)]) hμ.le

/-- `0 ≤ 1 - e^{-μ t} - μ t e^{-μ t} ≤ 1 - e^{-μ t}` for `μ t ≥ 0`. -/
lemma dissQ_bounds {μ t : ℝ} (h : 0 ≤ μ * t) :
    0 ≤ 1 - Real.exp (-μ * t) - μ * t * Real.exp (-μ * t) ∧
      1 - Real.exp (-μ * t) - μ * t * Real.exp (-μ * t) ≤ 1 - Real.exp (-μ * t) := by
  have hE := exp_neg_mul_mul_exp μ t
  have hpos := Real.exp_pos (-μ * t)
  have h1 := Real.add_one_le_exp (μ * t)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]
  · nlinarith [mul_nonneg h hpos.le]

lemma abs_dissZ_le {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (c : ℝ) :
    |dissZ μ c t| ≤ |c| / μ ^ 2 := by
  obtain ⟨hq0, hq1⟩ := dissQ_bounds (mul_nonneg hμ.le ht)
  have hE := Real.exp_pos (-μ * t)
  rw [dissZ, abs_div, abs_mul, abs_of_nonneg hq0, abs_of_pos (by positivity : (0 : ℝ) < μ ^ 2)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc |c| * (1 - Real.exp (-μ * t) - μ * t * Real.exp (-μ * t)) ≤ |c| * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    _ = |c| := mul_one _

/-- Along the dissipative solutions the distance to `M_{≤ k}` is `y(t)` for all `t ≥ 0`, if
`1/μ + |c|/μ² ≤ a`. -/
theorem distLR_dissSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a μ c t : ℝ}
    (hμ : 0 < μ) (ht : 0 ≤ t) (ha : 1 / μ + |c| / μ ^ 2 ≤ a) :
    distLR k (dissSol U V a μ c t) = dissY μ t := by
  have hy := dissY_le hμ t
  have hz := abs_dissZ_le hμ ht c
  have hz' := neg_abs_le (dissZ μ c t)
  have hc : 0 ≤ |c| / μ ^ 2 := by positivity
  exact distLR_frameCurve hk hU hV (dissY_nonneg hμ ht) (by linarith) (by linarith)

theorem hasDerivAt_exp_neg_mul (μ t : ℝ) :
    HasDerivAt (fun s => Real.exp (-μ * s)) (-μ * Real.exp (-μ * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (-μ)).exp
  refine h.congr_deriv ?_
  simp only [id, mul_one]
  ring

theorem hasDerivAt_dissY {μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) :
    HasDerivAt (dissY μ) (Real.exp (-μ * t)) t := by
  have h := ((hasDerivAt_exp_neg_mul μ t).const_sub 1).div_const μ
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_dissZ {μ : ℝ} (hμ : μ ≠ 0) (c t : ℝ) :
    HasDerivAt (dissZ μ c) (c * t * Real.exp (-μ * t)) t := by
  have h2 : HasDerivAt (fun s => μ * s) μ t := by
    simpa using (hasDerivAt_id t).const_mul μ
  have h := ((((hasDerivAt_exp_neg_mul μ t).const_sub 1).sub
    (h2.mul (hasDerivAt_exp_neg_mul μ t))).const_mul c).div_const (μ ^ 2)
  refine h.congr_deriv ?_
  rw [div_eq_iff (pow_ne_zero 2 hμ)]
  ring

/-- `1 - μ y = e^{-μ t}` and `c y - μ z_c = c t e^{-μ t}`: the equations of `y` and `z_c`. -/
lemma one_sub_mul_dissY {μ : ℝ} (hμ : μ ≠ 0) (t : ℝ) :
    1 - μ * dissY μ t = Real.exp (-μ * t) := by
  rw [dissY]
  field_simp
  ring

lemma mul_dissY_sub_mul_dissZ {μ : ℝ} (hμ : μ ≠ 0) (c t : ℝ) :
    c * dissY μ t - μ * dissZ μ c t = c * t * Real.exp (-μ * t) := by
  rw [dissY, dissZ]
  field_simp
  ring

theorem hasDerivAt_dissSol {μ : ℝ} (hμ : μ ≠ 0) (U : Matrix m (Fin (k + 1)) ℝ)
    (V : Matrix n (Fin (k + 1)) ℝ) (a c t : ℝ) :
    HasDerivAt (dissSol U V a μ c)
      ((c * t * Real.exp (-μ * t)) • frameW U V + Real.exp (-μ * t) • frameB U V) t :=
  (((hasDerivAt_dissZ hμ c t).smul_const (frameW U V)).const_add (frameStart U V a)).add
    ((hasDerivAt_dissY hμ t).smul_const (frameB U V))

/-- **The exact dissipative solutions.** For `0 < μ` and `1/μ + |c|/μ² ≤ a`, `A_c` solves
`y' = F_c(t, y)` on `[0, T]` for every `T`. -/
theorem odeSolution_dissSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a μ c T : ℝ}
    (hμ : 0 < μ) (ha : 1 / μ + |c| / μ ^ 2 ≤ a) :
    ODESolution (dissField U V a μ c) (dissSol U V a μ c) 0 T where
  cont := fun t _ => (hasDerivAt_dissSol hμ.ne' U V a c t).continuousAt.continuousWithinAt
  deriv t ht := by
    have e : dissField U V a μ c t (dissSol U V a μ c t) =
        (c * t * Real.exp (-μ * t)) • frameW U V + Real.exp (-μ * t) • frameB U V := by
      rw [dissField, distLR_dissSol hk hU hV hμ ht.1 ha, ← mul_dissY_sub_mul_dissZ hμ.ne',
        ← one_sub_mul_dissY hμ.ne', dissSol, frameCurve]
      module
    rw [e]
    exact (hasDerivAt_dissSol hμ.ne' U V a c t).hasDerivWithinAt

/-- Both dissipative fields equal `μ A₀ + B - μ Z` on `M_{≤ k}`. -/
theorem dissField_of_rank_le (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a μ c t : ℝ) {Z : Matrix m n ℝ} (hZ : Z.rank ≤ k) :
    dissField U V a μ c t Z = μ • frameStart U V a + frameB U V - μ • Z :=
  add_distLR_smul_of_rank_le (fun _ Z => μ • frameStart U V a + frameB U V - μ • Z)
    (frameW U V) c t hZ

/-- The dissipative field is one-sided Lipschitz with the constant `|c| - μ`; for `|c| ≤ μ` it
is dissipative. -/
theorem isOneSidedLipschitzField_dissField (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a μ c : ℝ) :
    IsOneSidedLipschitzField (dissField U V a μ c) (-μ + |c|) := by
  have h := isOneSidedLipschitzField_add_distLR_smul
    (isOneSidedLipschitzField_sub_smul (μ • frameStart U V a + frameB U V) μ) (frameW U V) c k
  rwa [norm_frameW hU hV, mul_one] at h

/-- The dissipative field is Lipschitz with the constant `μ + |c|` (for `0 ≤ μ`). -/
theorem isLipschitzField_dissField (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (a c : ℝ) {μ : ℝ}
    (hμ : 0 ≤ μ) : IsLipschitzField (dissField U V a μ c) (μ + |c|) := by
  have hG : IsLipschitzField
      (fun (_ : ℝ) (Z : Matrix m n ℝ) => μ • frameStart U V a + frameB U V - μ • Z) μ := by
    intro t X Y
    have e : (μ • frameStart U V a + frameB U V - μ • X) -
        (μ • frameStart U V a + frameB U V - μ • Y) = (-μ) • (X - Y) := by module
    change ‖(μ • frameStart U V a + frameB U V - μ • X) -
        (μ • frameStart U V a + frameB U V - μ • Y)‖ ≤ μ * ‖X - Y‖
    rw [e, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hμ]
  have h := isLipschitzField_add_distLR_smul hG (frameW U V) c k
  rwa [norm_frameW hU hV, mul_one] at h

omit [Fintype m] [Fintype n] in
theorem dissSol_zero (U : Matrix m (Fin (k + 1)) ℝ) (V : Matrix n (Fin (k + 1)) ℝ)
    (a μ c : ℝ) : dissSol U V a μ c 0 = frameStart U V a := by
  simp [dissSol, frameCurve, dissY, dissZ]

lemma dissZ_neg (μ c t : ℝ) : dissZ μ (-c) t = -dissZ μ c t := by
  simp only [dissZ]
  ring

lemma dissZ_eq_mul (μ c t : ℝ) : dissZ μ c t = c * dissZ μ 1 t := by
  simp only [dissZ]
  ring

/-- The two dissipative solutions differ by `2 z_L(T) W`. -/
theorem norm_dissSol_sub_dissSol (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) {a μ L T : ℝ}
    (hμ : 0 < μ) (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ‖dissSol U V a μ L T - dissSol U V a μ (-L) T‖ = 2 * dissZ μ L T := by
  have e : dissSol U V a μ L T - dissSol U V a μ (-L) T = (2 * dissZ μ L T) • frameW U V := by
    rw [dissSol, dissSol, frameCurve, frameCurve, dissZ_neg]
    module
  have hz : 0 ≤ dissZ μ L T := by
    rw [dissZ]
    exact div_nonneg (mul_nonneg hL (dissQ_bounds (mul_nonneg hμ.le hT)).1) (by positivity)
  rw [e, norm_smul, norm_frameW hU hV, mul_one, Real.norm_of_nonneg (by linarith)]

/-- `∫₀ᵀ e^{-μ (T - s)} y(s) ds = z_1(T)`, from the antiderivative `e^{-μ (T - s)} z_1(s)`. -/
theorem integral_exp_mul_dissY {μ : ℝ} (hμ : μ ≠ 0) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, Real.exp (-μ * (T - s)) * dissY μ s = dissZ μ 1 T := by
  have hd : ∀ s, HasDerivAt (fun s => Real.exp (-μ * (T - s)) * dissZ μ 1 s)
      (Real.exp (-μ * (T - s)) * dissY μ s) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (-μ * (T - s))) (Real.exp (-μ * (T - s)) * μ) s := by
      have h := (((hasDerivAt_id s).const_sub T).const_mul (-μ)).exp
      refine h.congr_deriv ?_
      simp only [id]
      ring
    have h := h1.mul (hasDerivAt_dissZ hμ 1 s)
    refine h.congr_deriv ?_
    have hy := mul_dissY_sub_mul_dissZ hμ 1 s
    have e : dissY μ s = μ * dissZ μ 1 s + 1 * s * Real.exp (-μ * s) := by linarith
    rw [e]
    ring
  have hc : Continuous fun s => Real.exp (-μ * (T - s)) * dissY μ s := by
    unfold dissY
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc.intervalIntegrable _ _)]
  simp [dissZ]

theorem integral_exp_distLR_dissSol (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a μ c T : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T) (ha : 1 / μ + |c| / μ ^ 2 ≤ a) :
    ∫ s in (0 : ℝ)..T, Real.exp (-μ * (T - s)) * distLR k (dissSol U V a μ c s) =
      dissZ μ 1 T := by
  rw [← integral_exp_mul_dissY hμ.ne' T]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hT] at hs
  rw [distLR_dissSol hk hU hV hμ hs.1 ha]

/-- **The identity of the dissipative pair.** For `c = L` and `c = -L`:
`‖A_L(T) - A_{-L}(T)‖ = 2 L ∫₀ᵀ e^{-μ (T - s)} dist(A_c(s), M_{≤ k}) ds`. -/
theorem norm_dissSol_sub_eq_two_mul_integral (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a μ L T c : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 1 / μ + L / μ ^ 2 ≤ a)
    (hc : c = L ∨ c = -L) :
    ‖dissSol U V a μ L T - dissSol U V a μ (-L) T‖ =
      2 * L * ∫ s in (0 : ℝ)..T, Real.exp (-μ * (T - s)) * distLR k (dissSol U V a μ c s) := by
  have hc' : |c| = L := by
    rcases hc with rfl | rfl
    · exact abs_of_nonneg hL
    · rw [abs_neg, abs_of_nonneg hL]
  rw [norm_dissSol_sub_dissSol hU hV hμ hL hT, integral_exp_distLR_dissSol hk hU hV hμ hT
    (by rwa [hc']), dissZ_eq_mul]
  ring

/-- **Lower bound in a dissipative class.** Every method whose output depends on the field only
through its values on `M_{≤ k}` has, for one of the two fields `F_L`, `F_{-L}` (one-sided
Lipschitz with the constant `L - μ`, Lipschitz with `μ + L`), error at least
`L ∫₀ᵀ e^{-μ (T - s)} dist(A(s), M_{≤ k}) ds`. -/
theorem mul_integral_exp_distLR_le_max_error (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a μ L T c : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 1 / μ + L / μ ^ 2 ≤ a)
    (hc : c = L ∨ c = -L)
    (Φ : (ℝ → Matrix m n ℝ → Matrix m n ℝ) → Matrix m n ℝ)
    (hΦ : ∀ F G : ℝ → Matrix m n ℝ → Matrix m n ℝ,
      (∀ t (Z : Matrix m n ℝ), Z.rank ≤ k → F t Z = G t Z) → Φ F = Φ G) :
    L * ∫ s in (0 : ℝ)..T, Real.exp (-μ * (T - s)) * distLR k (dissSol U V a μ c s) ≤
      max ‖Φ (dissField U V a μ L) - dissSol U V a μ L T‖
        ‖Φ (dissField U V a μ (-L)) - dissSol U V a μ (-L) T‖ := by
  have h := half_norm_sub_le_max_error (S := {p : ℝ × Matrix m n ℝ | p.2.rank ≤ k}) Φ
    (fun F G hFG => hΦ F G fun t Z hZ => hFG (t, Z) hZ)
    (F₁ := dissField U V a μ L) (F₂ := dissField U V a μ (-L))
    (fun p hp => by
      rw [dissField_of_rank_le U V a μ L p.1 hp, dissField_of_rank_le U V a μ (-L) p.1 hp])
    (dissSol U V a μ L T) (dissSol U V a μ (-L) T)
  rw [norm_dissSol_sub_eq_two_mul_integral hk hU hV hμ hL hT ha hc] at h
  linarith

/-- **The size of the necessary term in the dissipative class.** It is at most `L/μ` times the
distance of the solution to `M_{≤ k}` at the final time:
`L ∫₀ᵀ e^{-μ (T - s)} dist(A(s), M_{≤ k}) ds ≤ (L/μ) dist(A(T), M_{≤ k})`. -/
theorem mul_integral_exp_distLR_dissSol_le (hk : 1 ≤ k) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    {a μ L T c : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hT : 0 ≤ T) (ha : 1 / μ + |c| / μ ^ 2 ≤ a) :
    L * ∫ s in (0 : ℝ)..T, Real.exp (-μ * (T - s)) * distLR k (dissSol U V a μ c s) ≤
      L / μ * distLR k (dissSol U V a μ c T) := by
  rw [integral_exp_distLR_dissSol hk hU hV hμ hT ha, distLR_dissSol hk hU hV hμ hT ha, dissZ,
    dissY]
  have hq := (dissQ_bounds (mul_nonneg hμ.le hT)).2
  have e1 : L * (1 * (1 - Real.exp (-μ * T) - μ * T * Real.exp (-μ * T)) / μ ^ 2) =
      L / μ * ((1 - Real.exp (-μ * T) - μ * T * Real.exp (-μ * T)) / μ) := by
    field_simp
  rw [e1]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hq hμ.le) (by positivity)

/-- The necessary term is positive for `0 < L`, `0 < μ`, `0 < T`. -/
theorem dissZ_pos {μ L T : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hT : 0 < T) : 0 < dissZ μ L T := by
  have hE := exp_neg_mul_mul_exp μ T
  have hpos := Real.exp_pos (-μ * T)
  have h1 := Real.add_one_lt_exp (ne_of_gt (mul_pos hμ hT))
  have hq : 0 < 1 - Real.exp (-μ * T) - μ * T * Real.exp (-μ * T) := by
    nlinarith [mul_lt_mul_of_pos_left h1 hpos]
  rw [dissZ]
  positivity

end LeanDLRA.InformationLowerBoundGeneralExample

/-! ### Non-vacuity -/

namespace LeanDLRA.InformationLowerBoundGeneralExample

/-- The pair exists for `3 × 4` matrices, `k = 2`, `L = T = 1`, `a = 2`. -/
example : ∃ (F₁ F₂ : ℝ → Matrix (Fin 3) (Fin 4) ℝ → Matrix (Fin 3) (Fin 4) ℝ)
    (A₁ A₂ : ℝ → Matrix (Fin 3) (Fin 4) ℝ),
      IsLipschitzField F₁ 1 ∧ IsLipschitzField F₂ 1 ∧
      (∀ t (Z : Matrix (Fin 3) (Fin 4) ℝ), Z.rank ≤ 2 → F₁ t Z = F₂ t Z) ∧
      ODESolution F₁ A₁ 0 1 ∧ ODESolution F₂ A₂ 0 1 ∧ A₁ 0 = A₂ 0 ∧ (A₁ 0).rank ≤ 2 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, distLR 2 (A₁ t) = t ∧ distLR 2 (A₂ t) = t) ∧
      ‖A₁ 1 - A₂ 1‖ = 1 * 1 ^ 2 ∧
      ‖A₁ 1 - A₂ 1‖ = 2 * 1 * ∫ s in (0 : ℝ)..1, distLR 2 (A₁ s) ∧
      ‖A₁ 1 - A₂ 1‖ = 2 * 1 * ∫ s in (0 : ℝ)..1, distLR 2 (A₂ s) ∧
      ∀ Φ : (ℝ → Matrix (Fin 3) (Fin 4) ℝ → Matrix (Fin 3) (Fin 4) ℝ) → Matrix (Fin 3) (Fin 4) ℝ,
        (∀ F G : ℝ → Matrix (Fin 3) (Fin 4) ℝ → Matrix (Fin 3) (Fin 4) ℝ,
          (∀ t (Z : Matrix (Fin 3) (Fin 4) ℝ), Z.rank ≤ 2 → F t Z = G t Z) → Φ F = Φ G) →
        1 * ∫ s in (0 : ℝ)..1, distLR 2 (A₁ s) ≤ max ‖Φ F₁ - A₁ 1‖ ‖Φ F₂ - A₂ 1‖ :=
  InformationLowerBoundGeneral.exists_lowRank_information_pair (a := 2) (by norm_num) (by simp)
    (by simp) zero_le_one zero_le_one (by norm_num)

/-- The dissipative pair with `μ = L = 1` (one-sided constant `0`), `k = 1`, `2 × 2`, `a = 2`,
`T = 1`: every field-independent output has error at least `z_1(1) = 1 - 2/e > 0` for one of
the two fields. -/
example (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    0 < dissZ 1 1 1 ∧ IsOneSidedLipschitzField
      (dissField (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ) (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ) 2 1 1)
        (-1 + |1|) ∧
      dissZ 1 1 1 ≤ max ‖Y - dissSol (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ)
        (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ) 2 1 1 1‖
        ‖Y - dissSol (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ)
          (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ) 2 1 (-1) 1‖ := by
  have hU : (1 : Matrix (Fin 2) (Fin (1 + 1)) ℝ)ᵀ * 1 = 1 := by simp
  refine ⟨dissZ_pos one_pos one_pos one_pos,
    isOneSidedLipschitzField_dissField hU hU 2 1 1, ?_⟩
  have h := mul_integral_exp_distLR_le_max_error (k := 1) le_rfl hU hU (a := 2) (μ := 1) (L := 1)
    (T := 1) (c := 1) one_pos zero_le_one zero_le_one (by norm_num) (Or.inl rfl) (fun _ => Y)
    (fun _ _ _ => rfl)
  rw [integral_exp_distLR_dissSol le_rfl hU hU one_pos zero_le_one (by norm_num), one_mul] at h
  simpa only [norm_sub_rev] using h

end LeanDLRA.InformationLowerBoundGeneralExample

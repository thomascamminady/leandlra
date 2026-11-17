import LeanDLRA.Foundations.Localization

/-!
# Results of arXiv 2601.21428: Gramian bound for one projector-splitting step

Formalized: the first inequality of Props. 5.2 and 6.2 (Eqs. (55) and (64)), i.e. the Gramian
lower bound `C_{Y_{n+1}} ⪰ σ_B Δt I` after one step of the DLR projector-splitting schemes:
Algorithm 2 (Ũ from Eq. (14)) and Algorithm 3 (Ũ from Eq. (18)).  The right-hand side `G` of the
Gramian equation is kept general (a real `k × d` matrix), so one statement covers both algorithms.

Setting.  The random modes are vectors in a real inner product space `H`, read as `L²(Ω; ℝ)`.
The Gram matrix `C_Z = E[Z Zᵀ]` is `LeanDLRA.gramMatrix Z` (reused from
`Foundations/Localization.lean`), and `E[⟨·,·⟩]` is the inner product of `H`.  The deterministic
modes `U` are `k × d` with orthonormal rows, `U Uᵀ = 1`.  The projector `P_U` is `1 - Uᵀ U`.

Stochastic inputs.  The library has no stochastic calculus, so three facts from the paper's proof
enter as hypotheses, in the same way as in `LeanDLRA/Stochastic/MeanSquare.lean`:
* `horth`: martingale orthogonality `E[Yp_i ζ_j] = 0` between the `F_{t_n}`-measurable part
  `Yp` (`Y_n + U a Δt`) and the noise increment `ζ = U b ΔW` (paper, proof of Prop. 4.1, the
  remark that the terms linear in `ΔW` vanish);
* `hiso`: Itô isometry `E[ζ ζᵀ] = Δt U E[bbᵀ] Uᵀ` (paper, Eq. (29));
* `hB`: `E[bbᵀ] ⪰ σ_B I`, the expectation of Assumption 5 (`bbᵀ ⪰ σ_B I` pointwise).

Everything else is proved: the Gram lower bound of `Ỹ` (`σ_B Δt I` from the noise part),
invertibility of `C_Ỹ`, the identity `(Ũ - U) Uᵀ = 0` from the Gramian equation, the identity
`Rᵀ R = 1 + (Ũ - U)(Ũ - U)ᵀ` for the QR factor, the contraction `|Rᵀ v| ≥ |v|`, and the transfer
of the bound through `Y_{n+1} = R Ỹ`.

Main result: `projected_step_gram_lower_bound`.  With `Ũᵀ = Q R` (QR step, `Qᵀ Q = 1`),
`U_{n+1} = Qᵀ` and `Y_{n+1} = R Ỹ`, it proves `U_{n+1}ᵀ Y_{n+1} = Ũᵀ Ỹ` and
`C_{Y_{n+1}} ⪰ σ_B Δt I`.  The inequality is written as `σ_B Δt (vᵀv) ≤ vᵀ C v` for all `v`.

Not formalized: (i) the strict form `≻` of Eqs. (55) and (64); only the non-strict `⪰` is proved.
(ii) The uniform-step bounds (56) and (65), which need the `L²` bound of Lemma 5.1 and Assumption 4.
(iii) Algorithm 1 (Props. 4.1, 4.4), Theorems 4.6, 4.9, 5.3, 5.4, 5.5, 6.3 and the continuous
stability Prop. 5.7 (Itô calculus).  (iv) The mean-square bounds and stability statements that
`LeanDLRA/Stochastic/MeanSquare.lean` already covers are not repeated here.
-/

namespace LeanDLRA.Literature.P2601_21428

open scoped Matrix RealInnerProductSpace

variable {k d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A nonnegative quadratic form: `0 ≤ vᵀ v`. -/
lemma dot_self_nonneg_real {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- Moving a matrix across a bilinear pairing: `(A y) ⬝ x = y ⬝ (Aᵀ x)`. -/
lemma dotProduct_mulVec_swap {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (x : m → ℝ) (y : n → ℝ) : (A *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- The quadratic form of a Gram matrix: `vᵀ C_Z v = E|∑ vᵢ Zᵢ|²`. -/
lemma dotProduct_gram_mulVec (Z : PiLp 2 fun _ : Fin k => H) (v : Fin k → ℝ) :
    v ⬝ᵥ (LeanDLRA.gramMatrix Z *ᵥ v) = ‖∑ i, v i • Z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    Matrix.mulVec, dotProduct, LeanDLRA.gramMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (Z i) (Z j)]
  ring

/-- Orthogonal splitting: if `⟨Yp_i, ζ_j⟩ = 0` for all `i, j`, the noise part alone is dominated:
`|∑ vᵢ ζᵢ|² ≤ |∑ vᵢ (Ypᵢ + ζᵢ)|²`. -/
lemma norm_sq_noise_le_of_orth (Yp ζ : PiLp 2 fun _ : Fin k => H) (v : Fin k → ℝ)
    (horth : ∀ i j, ⟪Yp i, ζ j⟫ = 0) :
    ‖∑ i, v i • ζ i‖ ^ 2 ≤ ‖∑ i, v i • (Yp i + ζ i)‖ ^ 2 := by
  have hsum : ∑ i, v i • (Yp i + ζ i) = ∑ i, v i • Yp i + ∑ i, v i • ζ i := by
    simp only [smul_add, Finset.sum_add_distrib]
  have hcross : ⟪∑ i, v i • Yp i, ∑ i, v i • ζ i⟫ = 0 := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, horth,
      mul_zero, Finset.sum_const_zero]
  rw [hsum, norm_add_sq_real, hcross]
  nlinarith [sq_nonneg ‖∑ i, v i • Yp i‖]

/-- Noise Gram bound: if `B ⪰ σ I` then `U B Uᵀ ⪰ σ I` for `U Uᵀ = 1` (quadratic-form version). -/
lemma quad_noise_ge {U : Matrix (Fin k) (Fin d) ℝ} (hU : U * Uᵀ = 1) {B : Matrix (Fin d) (Fin d) ℝ}
    {σ : ℝ} (hB : ∀ w : Fin d → ℝ, σ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (B *ᵥ w)) (v : Fin k → ℝ) :
    σ * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((U * B * Uᵀ) *ᵥ v) := by
  have hnorm : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec_swap, Matrix.transpose_transpose, Matrix.mulVec_mulVec, hU,
      Matrix.one_mulVec]
  have h1 : (U * B * Uᵀ) *ᵥ v = U *ᵥ (B *ᵥ (Uᵀ *ᵥ v)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h2 : v ⬝ᵥ (U *ᵥ (B *ᵥ (Uᵀ *ᵥ v))) = (Uᵀ *ᵥ v) ⬝ᵥ (B *ᵥ (Uᵀ *ᵥ v)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [h1, h2, ← hnorm]
  exact hB _

/-- **Gramian lower bound after one projector-splitting step** (arXiv 2601.21428,
Props. 5.2 and 6.2,
first inequality of Eqs. (55) and (64), uniform-step-free form).

Data of one step:
* `U` is `k × d` with orthonormal rows (`U Uᵀ = 1`), `Yp` is the `F_{t_n}`-measurable part
  `Y_n + U a Δt`, `ζ` is the noise increment `U b ΔW`, `Yt = Ỹ = Yp + ζ`
  (hypothesis `hsplit`, Eqs. (14), (17)).
* `horth`: martingale orthogonality of `ζ` to `Yp` (see the module docstring).
* `hiso`, `hB`: Itô isometry `C_ζ = Δt U E[bbᵀ] Uᵀ` and `E[bbᵀ] ⪰ σ I` (Assumption 5, averaged).
* `Ut` solves the Gramian equation `C_Ỹ Ũ = C_Ỹ U + G (1 - Uᵀ U)` (Eq. (14) for Algorithm 2 and
  Eq. (18) for Algorithm 3; the matrix `G` is `Δt E[Ỹ aᵀ]` resp. the analogue with `ΔW bᵀ`).
* `Ũᵀ = Q R` with `Qᵀ Q = 1` is the QR step, and `Ynext = R Ỹ` is the new stochastic basis.

Conclusion, with the new deterministic basis `U_{n+1} = Qᵀ`:
* `U_{n+1}ᵀ Y_{n+1} = Ũᵀ Ỹ` (the projected update reproduces the basis-free increment);
* `σ Δt (vᵀ v) ≤ vᵀ C_{Y_{n+1}} v` for all `v`, i.e. `C_{Y_{n+1}} ⪰ σ Δt I`.

The paper's strict inequality `≻` is not claimed here.  Assumption 4 and the uniform-step bound
(56) are not used. -/
theorem projected_step_gram_lower_bound
    {U : Matrix (Fin k) (Fin d) ℝ} (hU : U * Uᵀ = 1)
    {Yp ζ Yt : PiLp 2 fun _ : Fin k => H} (hsplit : ∀ i, Yt i = Yp i + ζ i)
    (horth : ∀ i j, ⟪Yp i, ζ j⟫ = 0)
    {B : Matrix (Fin d) (Fin d) ℝ} {σ Δt : ℝ} (hσ : 0 < σ) (hΔt : 0 < Δt)
    (hB : ∀ w : Fin d → ℝ, σ * (w ⬝ᵥ w) ≤ w ⬝ᵥ (B *ᵥ w))
    (hiso : LeanDLRA.gramMatrix ζ = Δt • (U * B * Uᵀ))
    {G Ut : Matrix (Fin k) (Fin d) ℝ}
    (hUt : LeanDLRA.gramMatrix Yt * Ut = LeanDLRA.gramMatrix Yt * U + G * (1 - Uᵀ * U))
    {Q : Matrix (Fin d) (Fin k) ℝ} {R : Matrix (Fin k) (Fin k) ℝ}
    (hQR : Utᵀ = Q * R) (hQ : Qᵀ * Q = 1)
    {Ynext : PiLp 2 fun _ : Fin k => H} (hY : ∀ i, Ynext i = ∑ j, R i j • Yt j) :
    (∀ r : Fin d, ∑ i, Q r i • Ynext i = ∑ j, Utᵀ r j • Yt j) ∧
      ∀ v : Fin k → ℝ, σ * Δt * (v ⬝ᵥ v) ≤ v ⬝ᵥ (LeanDLRA.gramMatrix Ynext *ᵥ v) := by
  -- noise part of the Gram matrix of the noise increment
  have hζ : ∀ v : Fin k → ℝ, σ * Δt * (v ⬝ᵥ v) ≤ ‖∑ i, v i • ζ i‖ ^ 2 := by
    intro v
    rw [← dotProduct_gram_mulVec, hiso, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (quad_noise_ge hU hB v) hΔt.le]
  -- Gram lower bound of the intermediate modes
  have hYt : ∀ v : Fin k → ℝ, σ * Δt * (v ⬝ᵥ v) ≤ v ⬝ᵥ (LeanDLRA.gramMatrix Yt *ᵥ v) := by
    intro v
    have hsum : ∑ i, v i • Yt i = ∑ i, v i • (Yp i + ζ i) := by simp only [hsplit]
    rw [dotProduct_gram_mulVec, hsum]
    exact (hζ v).trans (norm_sq_noise_le_of_orth Yp ζ v horth)
  -- invertibility of the Gramian of the intermediate modes
  have hdet : IsUnit (LeanDLRA.gramMatrix Yt).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have hxy' : LeanDLRA.gramMatrix Yt *ᵥ x = LeanDLRA.gramMatrix Yt *ᵥ y := hxy
    have hz : LeanDLRA.gramMatrix Yt *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy', sub_self]
    have h0 := hYt (x - y)
    rw [hz, dotProduct_zero] at h0
    have hpos : 0 < σ * Δt := mul_pos hσ hΔt
    have h1 : (x - y) ⬝ᵥ (x - y) ≤ 0 := by
      nlinarith [hpos, h0]
    exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 (le_antisymm h1 (dot_self_nonneg_real _)))
  -- the deterministic increment `Ut - U` is orthogonal to the rows of `U`
  obtain ⟨D, rfl⟩ : ∃ D, Ut = U + D := ⟨Ut - U, by abel⟩
  have hCD : LeanDLRA.gramMatrix Yt * D = G * (1 - Uᵀ * U) := by
    rw [Matrix.mul_add] at hUt
    exact add_left_cancel hUt
  have hNU : (1 - Uᵀ * U) * Uᵀ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self]
  have hDU : D * Uᵀ = 0 := by
    have h1 : LeanDLRA.gramMatrix Yt * (D * Uᵀ) = 0 := by
      rw [← Matrix.mul_assoc, hCD, Matrix.mul_assoc, hNU, Matrix.mul_zero]
    have h2 := congrArg (fun M => (LeanDLRA.gramMatrix Yt)⁻¹ * M) h1
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
      Matrix.mul_zero] at h2
    exact h2
  have hUD0 : U * Dᵀ = 0 := by
    have h := congrArg Matrix.transpose hDU
    simpa [Matrix.transpose_mul] using h
  -- the QR factor: `Rᵀ R = 1 + D Dᵀ`
  have hRR : Rᵀ * R = 1 + D * Dᵀ := by
    have hT : U + D = Rᵀ * Qᵀ := by
      rw [← Matrix.transpose_transpose (U + D), hQR, Matrix.transpose_mul]
    have hNorm : (U + D) * (U + D)ᵀ = Rᵀ * R := by
      rw [hT]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [Matrix.mul_assoc Rᵀ Qᵀ (Q * R), ← Matrix.mul_assoc Qᵀ Q R, hQ, Matrix.one_mul]
    rw [← hNorm, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hU,
      hUD0, hDU]
    simp
  -- `|R x| ≥ |x|`
  have hmono : ∀ x : Fin k → ℝ, x ⬝ᵥ x ≤ (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
    intro x
    have h1 : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = x ⬝ᵥ ((Rᵀ * R) *ᵥ x) := by
      rw [dotProduct_mulVec_swap, Matrix.mulVec_mulVec]
    have h2 : x ⬝ᵥ ((Rᵀ * R) *ᵥ x) = x ⬝ᵥ x + (Dᵀ *ᵥ x) ⬝ᵥ (Dᵀ *ᵥ x) := by
      rw [hRR, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        dotProduct_comm x (D *ᵥ _), dotProduct_mulVec_swap]
    rw [h1, h2]
    linarith [dot_self_nonneg_real (Dᵀ *ᵥ x)]
  -- `R` is injective, hence bijective
  have hRinj : Function.Injective (R *ᵥ ·) := by
    intro x y hxy
    have hxy' : R *ᵥ x = R *ᵥ y := hxy
    have h0 : (x - y) ⬝ᵥ (x - y) ≤ 0 := by
      have := hmono (x - y)
      simpa [Matrix.mulVec_sub, hxy'] using this
    exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 (le_antisymm h0 (dot_self_nonneg_real _)))
  have hRunit : IsUnit R := (Matrix.mulVec_injective_iff_isUnit).1 hRinj
  have hRsurj : Function.Surjective (R *ᵥ ·) := (Matrix.mulVec_surjective_iff_isUnit).2 hRunit
  -- contraction of the transpose: `|v| ≤ |Rᵀ v|`
  have hkey : ∀ v : Fin k → ℝ, v ⬝ᵥ v ≤ (Rᵀ *ᵥ v) ⬝ᵥ (Rᵀ *ᵥ v) := by
    intro v
    obtain ⟨x, hx⟩ := hRsurj v
    have hx' : R *ᵥ x = v := hx
    have hp : v ⬝ᵥ v = x ⬝ᵥ (Rᵀ *ᵥ v) := by
      nth_rewrite 1 [← hx']
      exact dotProduct_mulVec_swap R v x
    have hxx : x ⬝ᵥ x ≤ v ⬝ᵥ v := by
      have := hmono x
      rwa [hx'] at this
    have hcs : (x ⬝ᵥ (Rᵀ *ᵥ v)) ^ 2 ≤ (x ⬝ᵥ x) * ((Rᵀ *ᵥ v) ⬝ᵥ (Rᵀ *ᵥ v)) := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (Rᵀ *ᵥ v)
      simpa only [dotProduct, sq] using this
    have hq : 0 ≤ (Rᵀ *ᵥ v) ⬝ᵥ (Rᵀ *ᵥ v) := dot_self_nonneg_real _
    have hp0 : 0 ≤ v ⬝ᵥ v := dot_self_nonneg_real _
    have h2 := mul_le_mul_of_nonneg_right hxx hq
    rw [← hp] at hcs
    have h1 : (v ⬝ᵥ v) ^ 2 ≤ (v ⬝ᵥ v) * ((Rᵀ *ᵥ v) ⬝ᵥ (Rᵀ *ᵥ v)) := hcs.trans h2
    nlinarith [h1, hq, hp0]
  refine ⟨fun r => ?_, fun v => ?_⟩
  · have hcoef : ∀ j, (U + D)ᵀ r j = ∑ i, Q r i * R i j := by
      intro j
      rw [hQR, Matrix.mul_apply]
    simp only [hY, hcoef, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  · have hw : ∑ i, v i • Ynext i = ∑ j, (Rᵀ *ᵥ v) j • Yt j := by
      simp only [hY, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    calc σ * Δt * (v ⬝ᵥ v) ≤ σ * Δt * ((Rᵀ *ᵥ v) ⬝ᵥ (Rᵀ *ᵥ v)) :=
          mul_le_mul_of_nonneg_left (hkey v) (mul_pos hσ hΔt).le
      _ ≤ (Rᵀ *ᵥ v) ⬝ᵥ (LeanDLRA.gramMatrix Yt *ᵥ (Rᵀ *ᵥ v)) := hYt _
      _ = v ⬝ᵥ (LeanDLRA.gramMatrix Ynext *ᵥ v) := by
          rw [dotProduct_gram_mulVec, dotProduct_gram_mulVec, hw]

/-- Non-vacuity: all hypotheses hold for `k = d = 1`, `H = ℝ`, `U = B = Ut = Q = R = 1`, `G = 0`,
`σ = Δt = 1`, `Yp = 0`, `ζ = Yt = Ynext = 1`. -/
example := projected_step_gram_lower_bound (k := 1) (d := 1) (H := ℝ) (U := 1) (by simp)
  (Yp := WithLp.toLp 2 fun _ : Fin 1 => (0 : ℝ)) (ζ := WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ))
  (Yt := WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ)) (fun i => by simp)
  (fun i j => by simp) (B := 1) (σ := 1) (Δt := 1) one_pos one_pos (fun w => by simp)
  (by ext i j; simp [LeanDLRA.gramMatrix, Subsingleton.elim i j]) (G := 0) (Ut := 1)
  (by simp) (Q := 1) (R := 1) (by simp) (by simp)
  (Ynext := WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ))
  (fun i => by simp [Matrix.one_apply, Subsingleton.elim i 0])

end LeanDLRA.Literature.P2601_21428

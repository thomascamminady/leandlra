import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Foundations.OneSided

/-!
# Results of arXiv 2610.41606 (Hu-Yu): energy-constrained implicit step-and-truncate

Formalized results.

* **Lemma 4.1 (SVD contraction)**: `svdTrunc_contract`, `svdTrunc_energy_le`. Real Frobenius
  matrices, not the paper's complex ones. `svdTrunc U d V S = U diag(d·1_S) Vᵀ` is the partial
  SVD truncation of `Z = U diag(d) Vᵀ` (orthonormal columns in `U`, `V`) keeping the singular
  indices in `S`, any subset as in the lemma (the truncation `T_θ` of (2.5) keeps the leading
  `r`). The operators `C_j`, `D_k` are arbitrary matrices. No singular-value gap is used.
* **Section 5.4 (residual control cannot select the root)**: `cubic_stage_roots` and
  `cubic_stage_root_eq_zero`, the scalar algebra for `z - τ z³ = 0`. Not formalized: the claim that
  the errors of the nonzero roots grow as `τ → 0`, since the paper gives no precise error there.
* **Theorem 5.1 (energy bound and uniqueness of the implicit stage)**, partial:
  `implicit_stage_energy_and_unique`. Proved: every solution in the energy ball satisfies the
  energy bound `E(Z) ≤ q_{n+1}`, and two solutions in the ball coincide. NOT formalized: the
  existence part, which the paper proves by Brouwer degree (Mathlib lacks it). Not restated: that
  the solution lies in the open ball (immediate from `q_{n+1} < Q²`, which is not assumed here)
  and that its SVD truncation satisfies the same bound (Lemma 4.1, `svdTrunc_energy_le`, for
  matrices). Setting: abstract real inner product space `E` (the paper's complex `H_h` with
  `Re ⟨·, ·⟩` is one), `A` continuous, symmetric and positive semidefinite (the paper's `A_h` is
  positive definite), `E(Z) = ⟪A Z, Z⟫`, `energyBall A Q` the closure of `{E < Q²}` (for `Q > 0`
  this is the paper's `Ω̄_Q = {E ≤ Q²}`, since `E(s Z) = s² E(Z)`), `G` the field `F(t_{n+1}, ·)`
  at one step.
* **Theorem 5.2 (robust error bound for implicit SAT)**: `sat_robust_error_bound`. Full statement,
  on an abstract real inner product space `E` (as for Theorem 5.1, this covers the paper's
  complex `H_h`), with the library's one-sided condition `IsOneSidedLipschitzOn` on an arbitrary
  set `K` in place of `Ω̄_Q`, and `T = t_N`. The summed bound (5.8) with `exp(μ T/(1 - ζ))` is
  proved by induction, not with the library's Grönwall lemmas.

Not formalized: Lemma 6.1 and Theorem 6.2 (mesh-robust first-order bound for reaction-diffusion,
which needs discrete Fourier analysis), and Section 7 (Vlasov–Poisson: Lemmas 7.1, 7.4,
Theorems 7.2, 7.3, 7.5).

Core definitions used: `IsOneSidedLipschitzOn` (`Foundations/OneSided.lean`) and the Frobenius
lemmas `LeanDLRA.Frobenius.norm_mul_of_orthonormal`, `norm_mul_transpose_of_orthonormal`,
`norm_sq_eq_sum` (`Matrix/Frobenius.lean`). Local additions: `svdTrunc` and `energyBall`.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2610_41606

/-! ### Lemma 4.1: SVD contraction of the one-sided energies -/

section SVDContraction

variable {m n k p q : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype p] [Fintype q]

/-- The Frobenius norm of `M * diagonal d` as a weighted column sum. -/
lemma norm_sq_mul_diagonal [DecidableEq k] (M : Matrix p k ℝ) (d : k → ℝ) :
    ‖M * Matrix.diagonal d‖ ^ 2 = ∑ j, d j ^ 2 * ∑ i, M i j ^ 2 := by
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
  simp only [Matrix.mul_diagonal, mul_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- The Frobenius norm of `diagonal d * M` as a weighted row sum. -/
lemma norm_sq_diagonal_mul [DecidableEq p] (d : p → ℝ) (M : Matrix p k ℝ) :
    ‖Matrix.diagonal d * M‖ ^ 2 = ∑ i, d i ^ 2 * ∑ j, M i j ^ 2 := by
  rw [LeanDLRA.Frobenius.norm_sq_eq_sum]
  simp only [Matrix.diagonal_mul, mul_pow, Finset.mul_sum]

/-- Shrinking the weights of a column scaling does not increase the Frobenius norm. -/
lemma norm_mul_diagonal_le [DecidableEq k] (M : Matrix p k ℝ) {d d' : k → ℝ}
    (h : ∀ j, d' j ^ 2 ≤ d j ^ 2) :
    ‖M * Matrix.diagonal d'‖ ≤ ‖M * Matrix.diagonal d‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_mul_diagonal M d',
    norm_sq_mul_diagonal M d]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (h j) (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Shrinking the weights of a row scaling does not increase the Frobenius norm. -/
lemma norm_diagonal_mul_le [DecidableEq k] (M : Matrix k n ℝ) {d d' : k → ℝ}
    (h : ∀ j, d' j ^ 2 ≤ d j ^ 2) :
    ‖Matrix.diagonal d' * M‖ ≤ ‖Matrix.diagonal d * M‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_diagonal_mul d' M,
    norm_sq_diagonal_mul d M]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (h i) (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The partial SVD truncation of `Z = U diag(d) Vᵀ` keeping the singular terms with index in `S`:
`U diag(d·1_S) Vᵀ`. The paper's `T_r` keeps the leading `r` terms. -/
def svdTrunc [DecidableEq k] (U : Matrix m k ℝ) (d : k → ℝ) (V : Matrix n k ℝ) (S : Finset k) :
    Matrix m n ℝ :=
  U * Matrix.diagonal (fun j => if j ∈ S then d j else 0) * Vᵀ

omit [Fintype k] in
lemma weight_sq_le [DecidableEq k] (d : k → ℝ) (S : Finset k) (j : k) :
    (if j ∈ S then d j else 0) ^ 2 ≤ d j ^ 2 := by
  split_ifs <;> simp [sq_nonneg]

lemma norm_left_svd [DecidableEq k] {V : Matrix n k ℝ} (hV : Vᵀ * V = 1) (C : Matrix p m ℝ)
    (X : Matrix m k ℝ) : ‖C * (X * Vᵀ)‖ = ‖C * X‖ := by
  rw [← Matrix.mul_assoc, LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV]

/-- **Lemma 4.1 (SVD contraction), Frobenius form.** For `Z = U diag(d) Vᵀ` with orthonormal
columns of `U` and `V`, every partial truncation `T = svdTrunc U d V S` satisfies `‖T‖ ≤ ‖Z‖`,
`‖C T‖ ≤ ‖C Z‖` for every matrix `C`, and `‖T D‖ ≤ ‖Z D‖` for every matrix `D`. -/
theorem svdTrunc_contract [DecidableEq k] {U : Matrix m k ℝ} {V : Matrix n k ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (d : k → ℝ) (S : Finset k) (Z : Matrix m n ℝ)
    (hZ : Z = U * Matrix.diagonal d * Vᵀ) :
    ‖svdTrunc U d V S‖ ≤ ‖Z‖ ∧
      (∀ C : Matrix p m ℝ, ‖C * svdTrunc U d V S‖ ≤ ‖C * Z‖) ∧
      (∀ D : Matrix n q ℝ, ‖svdTrunc U d V S * D‖ ≤ ‖Z * D‖) := by
  subst hZ
  have hd' := weight_sq_le d S
  refine ⟨?_, fun C => ?_, fun D => ?_⟩
  · unfold svdTrunc
    rw [LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV,
      LeanDLRA.Frobenius.norm_mul_of_orthonormal hU,
      LeanDLRA.Frobenius.norm_mul_transpose_of_orthonormal hV,
      LeanDLRA.Frobenius.norm_mul_of_orthonormal hU]
    simpa using norm_diagonal_mul_le (1 : Matrix k k ℝ) hd'
  · unfold svdTrunc
    rw [norm_left_svd hV C _, norm_left_svd hV C _, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact norm_mul_diagonal_le (C * U) hd'
  · have hTD : svdTrunc U d V S * D
        = U * (Matrix.diagonal (fun j => if j ∈ S then d j else 0) * (Vᵀ * D)) := by
      unfold svdTrunc
      simp only [Matrix.mul_assoc]
    have hZD : U * Matrix.diagonal d * Vᵀ * D = U * (Matrix.diagonal d * (Vᵀ * D)) := by
      simp only [Matrix.mul_assoc]
    rw [hTD, hZD, LeanDLRA.Frobenius.norm_mul_of_orthonormal hU,
      LeanDLRA.Frobenius.norm_mul_of_orthonormal hU]
    exact norm_diagonal_mul_le (Vᵀ * D) hd'

/-- **Lemma 4.1, energy form.** With `E(Z) = ‖Z‖² + Σ_j ‖C_j Z‖² + Σ_l ‖Z D_l‖²`, the truncation
does not increase the energy: `E(T_S Z) ≤ E(Z)`, with no singular-value gap. -/
theorem svdTrunc_energy_le [DecidableEq k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Matrix m k ℝ} {V : Matrix n k ℝ} (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (d : k → ℝ)
    (S : Finset k) (Z : Matrix m n ℝ) (hZ : Z = U * Matrix.diagonal d * Vᵀ)
    (C : ι → Matrix p m ℝ) (D : κ → Matrix n q ℝ) :
    ‖svdTrunc U d V S‖ ^ 2 + ∑ j, ‖C j * svdTrunc U d V S‖ ^ 2
        + ∑ l, ‖svdTrunc U d V S * D l‖ ^ 2 ≤
      ‖Z‖ ^ 2 + ∑ j, ‖C j * Z‖ ^ 2 + ∑ l, ‖Z * D l‖ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := svdTrunc_contract (p := p) (q := q) hU hV d S Z hZ
  exact add_le_add (add_le_add (pow_le_pow_left₀ (norm_nonneg _) h0 2)
    (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h1 (C j)) 2))
    (Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (norm_nonneg _) (h2 (D l)) 2)

end SVDContraction

/-! ### Section 5.4: residual control cannot select the root -/

/-- **Section 5.4, roots.** For `τ > 0`, the stage equation `z - τ z³ = 0` of `y' = y³` with
`y_n = 0` has exactly the roots `0` and `±τ^{-1/2}`; each has zero residual. -/
theorem cubic_stage_roots {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    z - τ * z ^ 3 = 0 ↔ z = 0 ∨ z = Real.sqrt (1 / τ) ∨ z = -Real.sqrt (1 / τ) := by
  have hs : Real.sqrt (1 / τ) ^ 2 = 1 / τ := Real.sq_sqrt (one_div_pos.mpr hτ).le
  have hτ' : τ * (1 / τ) = 1 := mul_one_div_cancel hτ.ne'
  constructor
  · intro h
    have hf : z * (1 - τ * z ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hf with h0 | h0
    · exact Or.inl h0
    · have hz2 : z ^ 2 = 1 / τ := by
        field_simp
        linarith
      have hz2' : z ^ 2 = Real.sqrt (1 / τ) ^ 2 := by rw [hs]; exact hz2
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz2' with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  · rintro (h | h | h)
    · rw [h]; ring
    · have hz2 : z ^ 2 = 1 / τ := by rw [h]; exact hs
      linear_combination (-τ * z) * hz2 - z * hτ'
    · have hz2 : z ^ 2 = 1 / τ := by rw [h, neg_sq]; exact hs
      linear_combination (-τ * z) * hz2 - z * hτ'

/-- **Section 5.4, restriction.** If `|z| ≤ Q` and `τ Q² < 1`, then `z - τ z³ = 0` forces `z = 0`:
the nonzero roots `±τ^{-1/2}` lie outside the ball. -/
theorem cubic_stage_root_eq_zero {τ Q z : ℝ} (hτ : 0 < τ) (hτQ : τ * Q ^ 2 < 1)
    (hz : |z| ≤ Q) (h : z - τ * z ^ 3 = 0) : z = 0 := by
  by_contra hz0
  have hf : z * (1 - τ * z ^ 2) = 0 := by linear_combination h
  have h1 : 1 - τ * z ^ 2 = 0 := (mul_eq_zero.1 hf).resolve_left hz0
  have hz2 : z ^ 2 ≤ Q ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg z) hz 2
    rwa [sq_abs] at this
  have : τ * z ^ 2 ≤ τ * Q ^ 2 := mul_le_mul_of_nonneg_left hz2 hτ.le
  linarith

/-! ### Theorem 5.1: energy bound and uniqueness of the implicit stage -/

section Implicit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The energy ball `Ω̄_Q`: the closure of `{Z : E(Z) < Q²}` with `E(Z) = ⟪A Z, Z⟫`. -/
def energyBall (A : E →L[ℝ] E) (Q : ℝ) : Set E :=
  closure {Z : E | ⟪A Z, Z⟫ < Q ^ 2}

/-- For symmetric positive semidefinite `A` and `c > 0`: `2⟪A x, y⟫ ≤ c E(x) + E(y)/c`. -/
lemma two_inner_le_energy {A : E →L[ℝ] E} (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hPSD : ∀ x, 0 ≤ ⟪A x, x⟫) {c : ℝ} (hc : 0 < c) (x y : E) :
    2 * ⟪A x, y⟫ ≤ c * ⟪A x, x⟫ + ⟪A y, y⟫ / c := by
  have hsym : ⟪A y, x⟫ = ⟪A x, y⟫ := by rw [hA, real_inner_comm]
  have h0 := hPSD (c • x - y)
  have hexp : ⟪A (c • x - y), c • x - y⟫
      = c ^ 2 * ⟪A x, x⟫ - 2 * c * ⟪A x, y⟫ + ⟪A y, y⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hsym]
    ring
  rw [hexp] at h0
  have key : 2 * c * ⟪A x, y⟫ ≤ c * (c * ⟪A x, x⟫) + ⟪A y, y⟫ := by linarith
  have hD : ⟪A y, y⟫ / c * c = ⟪A y, y⟫ := div_mul_cancel₀ _ hc.ne'
  refine le_of_mul_le_mul_left ?_ hc
  nlinarith [key, hD]

/-- **Theorem 5.1 (energy bound and uniqueness of the implicit stage), partial.**
Let `A` be symmetric positive semidefinite, `E(Z) = ⟪A Z, Z⟫`, `Ω̄_Q = energyBall A Q`. Assume the
energy growth `2⟪A Z, G Z⟫ ≤ c_Q (1 + E(Z))` on `Ω̄_Q`, the one-sided condition with constant `μ`
on `Ω̄_Q`, `τ μ < 1`, `E(Y) ≤ q_n`, and `E(r) ≤ ε²`, i.e. `‖r‖_E ≤ ε`. Let
`q_{n+1} = (q_n + c_Q τ + ε²/(ητ)) / (1 - (c_Q + η) τ)` with positive denominator. Then every
solution `Z ∈ Ω̄_Q` of `Z - Y - τ G(Z) = r` has `E(Z) ≤ q_{n+1}`, and two solutions in `Ω̄_Q`
coincide. The existence of a solution is NOT part of this statement. -/
theorem implicit_stage_energy_and_unique {A : E →L[ℝ] E} (hA : ∀ x y, ⟪A x, y⟫ = ⟪x, A y⟫)
    (hPSD : ∀ x, 0 ≤ ⟪A x, x⟫) (G : E → E) {Q cQ μ τ η ε qn : ℝ} {Y r : E}
    (hτ : 0 < τ) (hη : 0 < η) (hτμ : τ * μ < 1)
    (hgrow : ∀ Z ∈ energyBall A Q, 2 * ⟪A Z, G Z⟫ ≤ cQ * (1 + ⟪A Z, Z⟫))
    (hos : IsOneSidedLipschitzOn (fun _ => G) (energyBall A Q) μ)
    (hY : ⟪A Y, Y⟫ ≤ qn) (hr : ⟪A r, r⟫ ≤ ε ^ 2)
    (hden : 0 < 1 - (cQ + η) * τ) :
    (∀ Z ∈ energyBall A Q, Z - Y - τ • G Z = r →
        ⟪A Z, Z⟫ ≤ (qn + cQ * τ + ε ^ 2 / (η * τ)) / (1 - (cQ + η) * τ)) ∧
    (∀ Z₁ ∈ energyBall A Q, ∀ Z₂ ∈ energyBall A Q,
        Z₁ - Y - τ • G Z₁ = r → Z₂ - Y - τ • G Z₂ = r → Z₁ = Z₂) := by
  constructor
  · intro Z hZ hsol
    have hZY : Z - Y = τ • G Z + r := by rw [← hsol]; abel
    have hsymYZ : ⟪A Y, Z⟫ = ⟪A Z, Y⟫ := by rw [hA, real_inner_comm]
    -- energy identity: E(Z) - E(Y) + E(Z - Y) = 2⟪A Z, Z - Y⟫
    have hid : ⟪A Z, Z⟫ - ⟪A Y, Y⟫ + ⟪A (Z - Y), Z - Y⟫ = 2 * ⟪A Z, Z - Y⟫ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      linarith [hsymYZ]
    have hZY2 : ⟪A Z, Z - Y⟫ = τ * ⟪A Z, G Z⟫ + ⟪A Z, r⟫ := by
      rw [hZY, inner_add_right, real_inner_smul_right]
    have hpsdZY : 0 ≤ ⟪A (Z - Y), Z - Y⟫ := hPSD _
    have hcs := two_inner_le_energy hA hPSD (mul_pos hη hτ) Z r
    have hcsr : 2 * ⟪A Z, r⟫ ≤ η * τ * ⟪A Z, Z⟫ + ε ^ 2 / (η * τ) := by
      have : ⟪A r, r⟫ / (η * τ) ≤ ε ^ 2 / (η * τ) :=
        div_le_div_of_nonneg_right hr (mul_pos hη hτ).le
      linarith
    have hgZ : τ * (2 * ⟪A Z, G Z⟫) ≤ τ * (cQ * (1 + ⟪A Z, Z⟫)) :=
      mul_le_mul_of_nonneg_left (hgrow Z hZ) hτ.le
    have hbound : ⟪A Z, Z⟫ * (1 - (cQ + η) * τ) ≤ qn + cQ * τ + ε ^ 2 / (η * τ) := by
      nlinarith [hid, hZY2, hcsr, hgZ, hY, hpsdZY]
    rw [le_div_iff₀ hden]
    exact hbound
  · intro Z₁ h₁ Z₂ h₂ e₁ e₂
    have hW : Z₁ - Z₂ = τ • (G Z₁ - G Z₂) := by
      have := e₁.trans e₂.symm
      rw [smul_sub]
      linear_combination (norm := module) this
    have hone : ⟪G Z₁ - G Z₂, Z₁ - Z₂⟫ ≤ μ * ‖Z₁ - Z₂‖ ^ 2 := hos 0 Z₁ h₁ Z₂ h₂
    set W := Z₁ - Z₂ with hWdef
    have hn : ⟪W, W⟫ = τ * ⟪W, G Z₁ - G Z₂⟫ := by
      calc ⟪W, W⟫ = ⟪W, τ • (G Z₁ - G Z₂)⟫ := by rw [← hW]
        _ = τ * ⟪W, G Z₁ - G Z₂⟫ := real_inner_smul_right _ _ _
    have hcomm : ⟪W, G Z₁ - G Z₂⟫ = ⟪G Z₁ - G Z₂, W⟫ := real_inner_comm _ _
    have h1 : ‖W‖ ^ 2 = τ * ⟪G Z₁ - G Z₂, W⟫ := by
      rw [← real_inner_self_eq_norm_sq, hn, hcomm]
    have hsq : ‖W‖ ^ 2 ≤ τ * μ * ‖W‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hone hτ.le
      nlinarith [this, h1]
    have h0 : ‖W‖ ^ 2 ≤ 0 := by
      by_contra hc
      have := mul_pos (sub_pos.2 hτμ) (not_le.mp hc)
      nlinarith [this, hsq]
    have hW0 : W = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm h0 (sq_nonneg _)))
    exact sub_eq_zero.1 hW0

/-- Non-vacuity of Theorem 5.1: on `E = ℝ` with `A = id`, `G = 0`, `Y = r = 0`, `τ = 1/2`,
`μ = 0`, `c_Q = 0`, `η = 1`, `ε = 0`, `q_n = 0`, `Q = 1`, all hypotheses hold. -/
example : True := by
  have _h := implicit_stage_energy_and_unique (E := ℝ) (A := ContinuousLinearMap.id ℝ ℝ)
    (fun x y => by simp)
    (fun x => by simp only [ContinuousLinearMap.id_apply]; exact real_inner_self_nonneg)
    (fun _ => (0 : ℝ)) (Q := 1) (cQ := 0) (μ := 0) (τ := 1 / 2) (η := 1) (ε := 0) (qn := 0)
    (Y := 0) (r := 0) (by norm_num) (by norm_num) (by norm_num)
    (fun Z _ => by simp) (fun _ _ _ _ _ => by simp) (by simp) (by simp) (by norm_num)
  trivial

end Implicit

/-! ### Theorem 5.2: robust error bound for implicit SAT -/

section Robust

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `1 / (1 - z) ≤ exp (z / (1 - ζ))` for `0 ≤ z ≤ ζ < 1`. -/
lemma inv_one_sub_le_exp_div {z ζ : ℝ} (hz0 : 0 ≤ z) (hzζ : z ≤ ζ) (hζ : ζ < 1) :
    1 / (1 - z) ≤ Real.exp (z / (1 - ζ)) := by
  have h1 : 0 < 1 - ζ := by linarith
  have hpos : 0 < 1 - z := by linarith
  have hne : 1 - z ≠ 0 := hpos.ne'
  have h2 : 1 + z / (1 - z) ≤ Real.exp (z / (1 - z)) := by
    linarith [Real.add_one_le_exp (z / (1 - z))]
  have h3 : z / (1 - z) ≤ z / (1 - ζ) := div_le_div_of_nonneg_left hz0 h1 (by linarith)
  have h4 : 1 / (1 - z) = 1 + z / (1 - z) := by
    rw [one_add_div hne]
    congr 1
    ring
  calc 1 / (1 - z) = 1 + z / (1 - z) := h4
    _ ≤ Real.exp (z / (1 - z)) := h2
    _ ≤ Real.exp (z / (1 - ζ)) := Real.exp_le_exp.mpr h3

/-- **Theorem 5.2 (robust error bound for implicit SAT).** `K` is the energy region `Ω̄_Q`.
`F : ℝ → E → E` satisfies the one-sided condition with constant `μ ≥ 0` on `K`. The stages solve
`Ŷ^{n+1} - Y^n - τ_n F(t_{n+1}, Ŷ^{n+1}) = r_{n+1}` with `‖r_{n+1}‖ ≤ ε_n`, and the comparison
states solve `X^{n+1} - X^n - τ_n F(t_{n+1}, X^{n+1}) = d_{n+1}`. The truncation satisfies
`‖Y^{n+1} - Ŷ^{n+1}‖ ≤ θ_n`. Stages and comparison states lie in `K`, and `μ τ_n ≤ ζ < 1`.
Conclusion: for `n ≤ N`, `‖Y^n - X^n‖ ≤ exp(μ T/(1 - ζ)) (‖Y^0 - X^0‖ + Σ_{j<N} (‖d_{j+1}‖ +
ε_j + θ_j))` with `T = t_N`. In the statement, `r n = r_{n+1}` and `d n = d_{n+1}`. -/
theorem sat_robust_error_bound (F : ℝ → E → E) {K : Set E} {μ ζ : ℝ} (hμ : 0 ≤ μ)
    (hζ : ζ < 1) (hos : IsOneSidedLipschitzOn F K μ)
    (t τ ε θ : ℕ → ℝ) (Y Yh X d r : ℕ → E)
    (ht0 : t 0 = 0) (htau : ∀ n, t (n + 1) = t n + τ n) (hτ : ∀ n, 0 ≤ τ n)
    (hμτ : ∀ n, μ * τ n ≤ ζ)
    (hYh : ∀ n, Yh (n + 1) - Y n - τ n • F (t (n + 1)) (Yh (n + 1)) = r n)
    (hr : ∀ n, ‖r n‖ ≤ ε n)
    (hX : ∀ n, X (n + 1) - X n - τ n • F (t (n + 1)) (X (n + 1)) = d n)
    (hθ : ∀ n, ‖Y (n + 1) - Yh (n + 1)‖ ≤ θ n)
    (hK : ∀ n, Yh (n + 1) ∈ K ∧ X (n + 1) ∈ K) (N : ℕ) :
    ∀ n ≤ N, ‖Y n - X n‖ ≤ Real.exp (μ * t N / (1 - ζ)) *
      (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range N, (‖d j‖ + ε j + θ j)) := by
  have hεnn : ∀ n, 0 ≤ ε n := fun n => (norm_nonneg _).trans (hr n)
  have hθnn : ∀ n, 0 ≤ θ n := fun n => (norm_nonneg _).trans (hθ n)
  have htnn : ∀ n, 0 ≤ t n := by
    intro n
    induction n with
    | zero => rw [ht0]
    | succ n ih => rw [htau]; linarith [hτ n]
  have htmono : Monotone t :=
    monotone_nat_of_le_succ (fun n => by rw [htau]; linarith [hτ n])
  -- one-step estimate (5.7): (1 - τ μ) ‖ê‖ ≤ e_n + ‖d_{n+1}‖ + ε_n
  have hone : ∀ n, (1 - τ n * μ) * ‖Yh (n + 1) - X (n + 1)‖ ≤ ‖Y n - X n‖ + ‖d n‖ + ε n := by
    intro n
    have hΔ := hos (t (n + 1)) (Yh (n + 1)) (hK n).1 (X (n + 1)) (hK n).2
    have heq : Yh (n + 1) - X (n + 1) = (Y n - X n) + r n - d n
        + τ n • (F (t (n + 1)) (Yh (n + 1)) - F (t (n + 1)) (X (n + 1))) := by
      linear_combination (norm := module) hYh n - hX n
    generalize hv : Yh (n + 1) - X (n + 1) = v at heq hΔ ⊢
    generalize hΔdef : F (t (n + 1)) (Yh (n + 1)) - F (t (n + 1)) (X (n + 1)) = Δ at heq hΔ
    have hinner : ⟪Δ, v⟫ ≤ μ * ‖v‖ ^ 2 := hΔ
    have h1 : ⟪v, v⟫ = ⟪v, (Y n - X n) + r n - d n + τ n • Δ⟫ := by rw [← heq]
    have h2 : ⟪v, (Y n - X n) + r n - d n + τ n • Δ⟫
        = ⟪v, Y n - X n⟫ + ⟪v, r n⟫ - ⟪v, d n⟫ + τ n * ⟪v, Δ⟫ := by
      rw [inner_add_right, inner_sub_right, inner_add_right, real_inner_smul_right]
    have hA : ⟪v, Y n - X n⟫ ≤ ‖v‖ * ‖Y n - X n‖ := real_inner_le_norm _ _
    have hR : ⟪v, r n⟫ ≤ ‖v‖ * ε n :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hr n) (norm_nonneg _))
    have hD : -⟪v, d n⟫ ≤ ‖v‖ * ‖d n‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    have hT : τ n * ⟪v, Δ⟫ ≤ τ n * (μ * ‖v‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (hτ n)
      rw [real_inner_comm]
      exact hinner
    have hsq : ‖v‖ ^ 2 = ⟪v, v⟫ := (real_inner_self_eq_norm_sq v).symm
    have hkey : ‖v‖ ^ 2 ≤ ‖v‖ * (‖Y n - X n‖ + ‖d n‖ + ε n) + τ n * μ * ‖v‖ ^ 2 := by
      linarith [hA, hR, hD, hT, h1, h2, hsq]
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
    · rw [← h0, mul_zero]
      linarith [norm_nonneg (Y n - X n), hεnn n, norm_nonneg (d n)]
    · refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [hkey]
  -- the stage error: ‖Y^{n+1} - X^{n+1}‖ ≤ θ_n + ‖Ŷ^{n+1} - X^{n+1}‖
  have hstep : ∀ n, ‖Y (n + 1) - X (n + 1)‖ ≤ θ n + ‖Yh (n + 1) - X (n + 1)‖ := by
    intro n
    have := norm_sub_le_norm_sub_add_norm_sub (Y (n + 1)) (Yh (n + 1)) (X (n + 1))
    linarith [hθ n]
  have hG : ∀ n, 1 ≤ Real.exp (μ * t n / (1 - ζ)) := fun n =>
    Real.one_le_exp (div_nonneg (mul_nonneg hμ (htnn n)) (by linarith))
  have hmain : ∀ n, ‖Y n - X n‖ ≤ Real.exp (μ * t n / (1 - ζ)) *
      (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j)) := by
    intro n
    induction n with
    | zero => simp [ht0]
    | succ n ih =>
      have hGn : Real.exp (μ * t (n + 1) / (1 - ζ))
          = Real.exp (μ * t n / (1 - ζ)) * Real.exp (τ n * μ / (1 - ζ)) := by
        rw [← Real.exp_add, htau]
        congr 1
        ring
      have hexpκ : 1 ≤ Real.exp (τ n * μ / (1 - ζ)) * (1 - τ n * μ) := by
        have h := inv_one_sub_le_exp_div (z := τ n * μ) (ζ := ζ) (mul_nonneg (hτ n) hμ)
          (by linarith [hμτ n]) hζ
        have hpos : 0 < 1 - τ n * μ := by linarith [hμτ n]
        rwa [div_le_iff₀ hpos] at h
      -- ‖ê‖ ≤ exp κ · (e_n + ‖d_{n+1}‖ + ε_n)
      have hê : ‖Yh (n + 1) - X (n + 1)‖
          ≤ Real.exp (τ n * μ / (1 - ζ)) * (‖Y n - X n‖ + ‖d n‖ + ε n) := by
        have hx0 : 0 ≤ ‖Yh (n + 1) - X (n + 1)‖ := norm_nonneg _
        calc ‖Yh (n + 1) - X (n + 1)‖ = ‖Yh (n + 1) - X (n + 1)‖ * 1 := (mul_one _).symm
          _ ≤ ‖Yh (n + 1) - X (n + 1)‖ *
              (Real.exp (τ n * μ / (1 - ζ)) * (1 - τ n * μ)) :=
              mul_le_mul_of_nonneg_left hexpκ hx0
          _ = Real.exp (τ n * μ / (1 - ζ)) * ((1 - τ n * μ) * ‖Yh (n + 1) - X (n + 1)‖) := by
              ring
          _ ≤ Real.exp (τ n * μ / (1 - ζ)) * (‖Y n - X n‖ + ‖d n‖ + ε n) :=
              mul_le_mul_of_nonneg_left (hone n) (Real.exp_pos _).le
      have hsplit : ‖Y (n + 1) - X (n + 1)‖
          ≤ θ n + Real.exp (τ n * μ / (1 - ζ)) * (‖Y n - X n‖ + ‖d n‖ + ε n) :=
        (hstep n).trans (by linarith [hê])
      have hA1 : Real.exp (τ n * μ / (1 - ζ)) * ‖Y n - X n‖ ≤ Real.exp (μ * t (n + 1) / (1 - ζ)) *
          (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j)) := by
        rw [hGn]
        calc Real.exp (τ n * μ / (1 - ζ)) * ‖Y n - X n‖
            ≤ Real.exp (τ n * μ / (1 - ζ)) * (Real.exp (μ * t n / (1 - ζ)) *
              (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j))) :=
              mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
          _ = Real.exp (μ * t n / (1 - ζ)) * Real.exp (τ n * μ / (1 - ζ)) *
              (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j)) := by ring
      have hA2 : Real.exp (τ n * μ / (1 - ζ)) * (‖d n‖ + ε n)
          ≤ Real.exp (μ * t (n + 1) / (1 - ζ)) * (‖d n‖ + ε n) := by
        rw [hGn]
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (Real.exp_pos _).le
          (hG n)) (add_nonneg (norm_nonneg _) (hεnn n))
      have hA3 : θ n ≤ Real.exp (μ * t (n + 1) / (1 - ζ)) * θ n :=
        le_mul_of_one_le_left (hθnn n) (hG (n + 1))
      have hS : ∑ j ∈ Finset.range (n + 1), (‖d j‖ + ε j + θ j)
          = ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j) + (‖d n‖ + ε n + θ n) :=
        Finset.sum_range_succ _ _
      rw [hS]
      nlinarith [hsplit, hA1, hA2, hA3]
  intro n hn
  calc ‖Y n - X n‖ ≤ Real.exp (μ * t n / (1 - ζ)) *
        (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range n, (‖d j‖ + ε j + θ j)) := hmain n
    _ ≤ Real.exp (μ * t N / (1 - ζ)) *
        (‖Y 0 - X 0‖ + ∑ j ∈ Finset.range N, (‖d j‖ + ε j + θ j)) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (htmono hn) hμ) (by linarith))
      · exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 hn) fun j _ _ =>
          add_nonneg (add_nonneg (norm_nonneg _) (hεnn j)) (hθnn j))
      · exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ =>
          add_nonneg (add_nonneg (norm_nonneg _) (hεnn j)) (hθnn j))
      · exact (Real.exp_pos _).le

/-- Non-vacuity of Theorem 5.2: with `F = 0` on `ℝ`, `K = ℝ`, `t_n = n`, `τ_n = 1`, all states and
defects `0`, every hypothesis holds. -/
example : True := by
  have _h := sat_robust_error_bound (E := ℝ) (F := fun _ _ => (0 : ℝ)) (K := Set.univ)
    (μ := 0) (ζ := 1 / 2) (t := fun n => (n : ℝ)) (τ := fun _ => 1) (ε := fun _ => 0)
    (θ := fun _ => 0) (Y := fun _ => 0) (Yh := fun _ => 0) (X := fun _ => 0)
    (d := fun _ => 0) (r := fun _ => 0) le_rfl (by norm_num) (fun _ x _ y _ => by simp)
    (by simp) (fun n => by simp) (fun _ => zero_le_one) (fun _ => by norm_num)
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) 3
  trivial

end Robust

end LeanDLRA.Literature.P2610_41606

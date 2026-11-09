import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Classical.SVD
import LeanDLRA.OpenProblems.Curated.Classicala
import LeanDLRA.Literature.Training.P2602_06208a

/-!
# Results of arXiv 2511.04485: Q3R reweighted rank regularizer

Ghosh, Nguyen, Kümmerle.  Everything here is stated for real rectangular matrices
`W ∈ ℝ^{d₁ × d₂}` with the Frobenius inner product and with Mathlib's singular values (`sv W i`,
zero-based, so that the paper's `σ_{r+1}` is `sv W r`); nothing is reduced to an abstract core.
The objects are the `ε`-smoothed log-determinant `F_ε` of eq. (1) (`FEps`), the reweighting operator
of Definition 4.1 (`reweight`, independent of the chosen SVD by `reweight_eq`), the quadratic model
of eq. (2) (`quadModel`), the regularizer of eq. (6) (`Q3R`) and `r(W, ε)` of eq. (3) (`rankEnv`).
**Lemma 4.1**: part 1 is `reweight_symm`, `reweight_pos`, `le_inner_reweight`, `Q3R_nonneg`,
`Q3R_eq_zero_iff`; part 2, eq. (4), is `reweight_eq_four_blocks`, with the block structure in
`reweight_leftProj`, `reweight_rightProj`; part 3, eq. (5), is `quadModel_eq`, with the true
gradient of `F_ε`.  **Lemma A.2**: `hasGradientAt_FEps`, `differentiable_FEps`, `gradient_FEps`
(eq. (10)) and `lipschitzWith_gradient_FEps`, the `1`-Lipschitz gradient that the paper claims
without proof.  **Lemma A.4**: `reweight_self_eq_gradient` (eq. (13)), `gradient_Q3R_self`.
Section 4.2: `hasGradientAt_Q3R`.  Appendix A.1: `FEps_nonneg`, `FEps_eq_half_sq`.

**Two claims the paper leaves unproved are theorems here.**  `FEps_le_quadModel` is the
majorization `F_ε(W) ≤ Q_ε(W | W')` for all `W`, `W'`, on which the authors say in footnote 2 that a
proof is beyond the scope of the paper.  `inner_genHessian_le` is the Loewner bound
`∂²F_ε(W') ⪯ R_{W',ε}` for generalized Hessians in the sense of Hiriart-Urruty, Strodiot and Nguyen
(`genHessian`; `id_mem_genHessian` shows that the set is not empty), and `inner_hessian_le` is its
form at points of twice differentiability.  The paper has no proof of either.

**A false claim.**  Section 4.1 (p. 6, after eq. (7)) says that `R_{W',ε}(W)` tends to `0` if `ε`
follows the dynamics of (7) and `ε → 0`, for `W` whose column and row spaces are orthogonal to the
columns of `U` and `V`.  This is the wrong way round: eq. (4) gives such `W` the weight one, so that
`R_{W',ε}(W) = W` for every `W'` and every `ε > 0`, with `U`, `V` the leading `r(W', ε)` singular
vectors of Definition 4.1 (`reweight_eq_self_of_orthogonal`).  Hence the claim fails along every
sequence `(W'_k, ε_k)`, in particular along the dynamics (7), where the expansion point changes
with `ε` (`not_tendsto_reweight_zero_seq`), and for a fixed `W'` and `ε → 0`
(`not_tendsto_reweight_zero`).  `exists_orthogonal_ne_zero` gives such `W ≠ 0` for every `W'`
without full rank, and the correct statement for a fixed `W'` is `tendsto_reweight`,
`tendsto_reweight_zero_iff`: `R_{W',ε}(W) → (I - U Uᵀ) W (I - V Vᵀ)`.

**The proofs differ from the paper's.**  The paper quotes the Lewis-Sendov theorem for Lemma A.2.
Here everything rests on the identity `sq_norm_conj_sub`,
`‖E X Eᵀ - F Y Fᵀ‖² = ∑ᵢⱼ (Eᵀ F)ᵢⱼ² (xᵢ - yⱼ)²`, and the doubly stochastic weights `(Eᵀ F)ᵢⱼ²`.
They give the variational bound `F_ε(Y) ≤ ½ tr(Y M Yᵀ) - ½ ε² log det M` for `0 < M ≤ I`
(`FEps_le_trace`), attained at `M = max (|Y| / ε, I)⁻²` (`FEps_eq_trace`).  Hence
`F_ε(Y) ≤ F_ε(Y a) - ε² log |det a|` for invertible contractions `a` (`FEps_le_FEps_mul`), and two
applications with the square roots of the two weights of `R_{W',ε}` give the majorization, without
Horn's inequality or weak majorization.  The Lipschitz bound applies the same identity to the
Jordan-Wielandt dilation (`norm_reweight_self_sub_le`), and differentiability then follows from the
majorization (`abs_FEps_sub_le`).  Lemma A.4 is proved first and its formula is what gives eq. (10).

**Algorithms 1 and 2**: `updateEps` is eq. (7), and `adamQ3R` is Algorithm 2 for an arbitrary
sequence of minibatch gradient maps.  Proved: `ε` does not increase (`updateEps_le`,
`adamQ3R_eps_antitone`), the expansion point is the iterate of the last reweighting step
(`adamQ3R_center`), the moments do not see the Q3R term (`adamQ3R_m_succ`, `adamQ3R_v_succ`),
line 13 holds with `R_t = ∇Q3R` (`adamQ3R_W_succ`, `hasGradientAt_Q3R`), and the rank envelope is at
most the target rank if `σ_{r+1}(W) ≤ ε_old` (`rankEnv_updateEps_le`, `adamQ3R_rankEnv_le`), while
it exceeds it otherwise (`lt_rankEnv_updateEps`).  Additions to the paper: `ε` stays positive iff
`rank W > r_target` (`updateEps_pos_iff`), a condition the paper does not state although Definition
4.1 needs `ε > 0`; and `F_ε` decreases along a frozen-operator iteration (`mm_descent`,
`Q3R_sub_smul_le`, `FEps_period_le`), the majorization-minimization descent.  Two remarks on the
paper.  The initial value `ε = ∞` is replaced by any real `ε₀ ≥ σ_{r+1}(W₀)`.  Line 1 of Algorithm 1
computes a partial SVD of order `r(W, ε_old)`, but `r(W, ε_new) ≥ r(W, ε_old)` (`rankEnv_anti`), so
the restriction in line 4 can need more columns than were computed.

Not formalized: Proposition A.1 (the general Lewis-Sendov theorem, only cited in the paper),
eq. (11) (a rewriting of eq. (10)), the non-convexity of Remark A.3, the operation counts of
Appendix B, convergence of Adam, and the heuristic statements on avoiding high-rank local minima.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2511_04485

open Matrix LeanDLRA.Literature.P2602_06208

noncomputable section

/-! ### The scalar functions -/

section Scalar

variable {ε σ m x y : ℝ}

/-- The scalar function `f_ε` of eq. (1) of arXiv 2511.04485. -/
def fEps (ε σ : ℝ) : ℝ :=
  if ε ≤ σ then ε ^ 2 * (Real.log σ - Real.log ε) + 1 / 2 * ε ^ 2 else 1 / 2 * σ ^ 2

/-- The weight `max (σ / ε) 1` of Definition 4.1 of arXiv 2511.04485. -/
def dEps (ε σ : ℝ) : ℝ := max (σ / ε) 1

lemma one_le_dEps : 1 ≤ dEps ε σ := le_max_right _ _

lemma dEps_pos : 0 < dEps ε σ := one_pos.trans_le one_le_dEps

lemma dEps_of_le (hε : 0 < ε) (h : σ ≤ ε) : dEps ε σ = 1 := max_eq_right ((div_le_one hε).2 h)

lemma dEps_of_ge (hε : 0 < ε) (h : ε ≤ σ) : dEps ε σ = σ / ε :=
  max_eq_left ((one_le_div hε).2 h)

lemma fEps_zero (hε : 0 < ε) : fEps ε 0 = 0 := by
  simp [fEps, not_le.2 hε]

/-- `f_ε(σ) = ½ σ² / d² + ε² log d` for the optimal weight `d = max (σ / ε) 1`. -/
lemma fEps_eq (hε : 0 < ε) :
    fEps ε σ = 1 / 2 * σ ^ 2 * (dEps ε σ ^ 2)⁻¹ + ε ^ 2 * Real.log (dEps ε σ) := by
  unfold fEps
  split_ifs with h
  · have hσ' : 0 < σ := hε.trans_le h
    rw [dEps_of_ge hε h, Real.log_div hσ'.ne' hε.ne']
    field_simp
    ring
  · rw [dEps_of_le hε (not_le.1 h).le]
    simp

/-- The variational inequality behind the majorization:
`f_ε(σ) ≤ ½ σ² m - ½ ε² log m` for every `m ∈ (0, 1]`. -/
lemma fEps_le (hε : 0 < ε) (hσ : 0 ≤ σ) (hm0 : 0 < m) (hm1 : m ≤ 1) :
    fEps ε σ ≤ 1 / 2 * σ ^ 2 * m - ε ^ 2 / 2 * Real.log m := by
  unfold fEps
  split_ifs with h
  · have hσ' : 0 < σ := hε.trans_le h
    have hy : 0 < σ ^ 2 * m / ε ^ 2 := by positivity
    have h1 := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hm0.ne',
      Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    have h2 : ε ^ 2 / 2 * (2 * Real.log σ + Real.log m - 2 * Real.log ε) ≤
        ε ^ 2 / 2 * (σ ^ 2 * m / ε ^ 2 - 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ε ^ 2 / 2 * (σ ^ 2 * m / ε ^ 2 - 1) = 1 / 2 * σ ^ 2 * m - ε ^ 2 / 2 := by
      field_simp
    rw [h3] at h2
    nlinarith
  · have h1 : σ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hσ (not_le.1 h).le 2
    have h2 := Real.log_le_sub_one_of_pos hm0
    have h3 : 0 ≤ (ε ^ 2 - σ ^ 2) * (1 - m) := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hm1)
    have h4 : ε ^ 2 * Real.log m ≤ ε ^ 2 * (m - 1) := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

/-- The weight `q(t) = max (√t / ε, 1)⁻²`, so that `q(σ²) σ` is the gradient of `f_ε` at `σ`. -/
def qEps (ε t : ℝ) : ℝ := (dEps ε √t ^ 2)⁻¹

/-- The odd extension `x ↦ x q(x²)` of `f_ε'`: it is `x` for `|x| ≤ ε` and `ε² / x` for
`|x| ≥ ε`. -/
def phiEps (ε x : ℝ) : ℝ := x * qEps ε (x ^ 2)

lemma phiEps_of_abs_le (hε : 0 < ε) (h : |x| ≤ ε) : phiEps ε x = x := by
  rw [phiEps, qEps, Real.sqrt_sq_eq_abs, dEps_of_le hε h]
  simp

lemma phiEps_of_le_abs (hε : 0 < ε) (h : ε ≤ |x|) : phiEps ε x = ε ^ 2 / x := by
  have hx : 0 < |x| := hε.trans_le h
  have hx0 : x ≠ 0 := abs_pos.1 hx
  rw [phiEps, qEps, Real.sqrt_sq_eq_abs, dEps_of_ge hε h, div_pow, sq_abs]
  field_simp

lemma phiEps_neg (ε x : ℝ) : phiEps ε (-x) = -phiEps ε x := by
  simp [phiEps]

private lemma abs_sub_div_le (hε : 0 < ε) (hx : |x| ≤ ε) (hy : ε ≤ y) :
    |x - ε ^ 2 / y| ≤ y - x := by
  have hy0 : 0 < y := hε.trans_le hy
  have hz : ε ^ 2 / y * y = ε ^ 2 := div_mul_cancel₀ _ hy0.ne'
  have hz0 : 0 < ε ^ 2 / y := by positivity
  set z := ε ^ 2 / y
  have hzy : z ≤ y := by nlinarith
  have hsum : 2 * ε ≤ y + z := by nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 2 * ε)]
  have hx' := abs_le.1 hx
  rw [abs_le]
  constructor <;> linarith

/-- `f_ε'` (extended oddly) is `1`-Lipschitz. -/
lemma abs_phiEps_sub_le (hε : 0 < ε) (x y : ℝ) : |phiEps ε x - phiEps ε y| ≤ |x - y| := by
  have key : ∀ a b : ℝ, |a| ≤ ε → ε ≤ |b| → |phiEps ε a - phiEps ε b| ≤ |a - b| := by
    intro a b ha hb
    rw [phiEps_of_abs_le hε ha, phiEps_of_le_abs hε hb]
    rcases le_total 0 b with h0 | h0
    · rw [abs_of_nonneg h0] at hb
      have h1 := abs_sub_div_le hε ha hb
      refine h1.trans ?_
      rw [abs_sub_comm]
      exact le_abs_self _
    · rw [abs_of_nonpos h0] at hb
      have h1 := abs_sub_div_le (x := -a) hε (by rwa [abs_neg]) hb
      have h2 : -a - ε ^ 2 / -b = -(a - ε ^ 2 / b) := by
        rw [div_neg]
        ring
      rw [h2, abs_neg] at h1
      refine h1.trans ?_
      have h3 : -b - -a = a - b := by ring
      rw [h3]
      exact le_abs_self _
  rcases le_total |x| ε with hx | hx <;> rcases le_total |y| ε with hy | hy
  · rw [phiEps_of_abs_le hε hx, phiEps_of_abs_le hε hy]
  · exact key x y hx hy
  · rw [abs_sub_comm, abs_sub_comm x]
    exact key y x hy hx
  · rw [phiEps_of_le_abs hε hx, phiEps_of_le_abs hε hy]
    have hx0 : 0 < |x| := hε.trans_le hx
    have hy0 : 0 < |y| := hε.trans_le hy
    have hx1 : x ≠ 0 := abs_pos.1 hx0
    have hy1 : y ≠ 0 := abs_pos.1 hy0
    have h1 : ε ^ 2 / x - ε ^ 2 / y = (y - x) * (ε ^ 2 / (x * y)) := by
      field_simp
    have h2 : |ε ^ 2 / (x * y)| ≤ 1 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ε ^ 2)]
      rw [div_le_one (by positivity)]
      nlinarith
    rw [h1, abs_mul, abs_sub_comm y x]
    exact mul_le_of_le_one_right (abs_nonneg _) h2

end Scalar

/-! ### Conjugated diagonal matrices: the double sum identity -/

section Spectral

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Spectral theorem in the form used here.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem exists_eig {A : Matrix k k ℝ} (hA : Aᵀ = A) :
    ∃ (E : Matrix k k ℝ) (a : k → ℝ), Eᵀ * E = 1 ∧ A = E * diagonal a * Eᵀ := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  have hspec := hH.spectral_theorem
  have hUm : (hH.eigenvectorUnitary : Matrix k k ℝ) ∈ Matrix.unitaryGroup k ℝ :=
    (hH.eigenvectorUnitary).2
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_⟩
  · have h := (Matrix.mem_unitaryGroup_iff'.1 hUm)
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  · have h2 : A = (hH.eigenvectorUnitary : Matrix k k ℝ) * diagonal hH.eigenvalues *
        star (hH.eigenvectorUnitary : Matrix k k ℝ) := by
      simpa using hspec
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2

lemma sum_sq_row {C : Matrix k k ℝ} (hC : C * Cᵀ = 1) (i : k) : ∑ j, C i j ^ 2 = 1 := by
  have h := congrFun (congrFun hC i) i
  simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq] at h
  simpa [sq] using h

lemma sum_sq_col {C : Matrix k k ℝ} (hC : Cᵀ * C = 1) (j : k) : ∑ i, C i j ^ 2 = 1 := by
  have h := congrFun (congrFun hC j) j
  simp only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq] at h
  simpa [sq] using h

lemma orth_mul {E F : Matrix k k ℝ} (hE : Eᵀ * E = 1) (hF : Fᵀ * F = 1) :
    (Eᵀ * F)ᵀ * (Eᵀ * F) = 1 := by
  have hE' : E * Eᵀ = 1 := mul_eq_one_comm.mp hE
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc E,
    hE', Matrix.one_mul, hF]

lemma orth_mul' {E F : Matrix k k ℝ} (hE : Eᵀ * E = 1) (hF : Fᵀ * F = 1) :
    (Eᵀ * F) * (Eᵀ * F)ᵀ = 1 :=
  mul_eq_one_comm.mp (orth_mul hE hF)

/-- The double sum identity: for orthogonal `E`, `F`,
`‖E X Eᵀ - F Y Fᵀ‖² = ∑ᵢⱼ (Eᵀ F)ᵢⱼ² (xᵢ - yⱼ)²`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem sq_norm_conj_sub {E F : Matrix k k ℝ} (hE : Eᵀ * E = 1) (hF : Fᵀ * F = 1) (x y : k → ℝ) :
    ‖E * diagonal x * Eᵀ - F * diagonal y * Fᵀ‖ ^ 2 =
      ∑ i, ∑ j, (Eᵀ * F) i j ^ 2 * (x i - y j) ^ 2 := by
  have hE' : E * Eᵀ = 1 := mul_eq_one_comm.mp hE
  have hF' : F * Fᵀ = 1 := mul_eq_one_comm.mp hF
  set Z := E * diagonal x * Eᵀ - F * diagonal y * Fᵀ with hZ
  have h1 : ‖Eᵀ * (Z * Fᵀᵀ)‖ = ‖Z‖ := by
    rw [Frobenius.norm_mul_of_orthonormal (by rwa [Matrix.transpose_transpose]),
      Frobenius.norm_mul_transpose_of_orthonormal (V := Fᵀ) (by rwa [Matrix.transpose_transpose])]
  have h2 : Eᵀ * (Z * Fᵀᵀ) = diagonal x * (Eᵀ * F) - (Eᵀ * F) * diagonal y := by
    rw [Matrix.transpose_transpose, hZ, Matrix.sub_mul, Matrix.mul_sub]
    congr 1
    · calc Eᵀ * (E * diagonal x * Eᵀ * F) = (Eᵀ * E) * diagonal x * (Eᵀ * F) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.one_mul]
    · calc Eᵀ * (F * diagonal y * Fᵀ * F) = Eᵀ * F * diagonal y * (Fᵀ * F) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hF, Matrix.mul_one]
  rw [← h1, h2, Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

/-- Matrix functions are independent of the diagonalization.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem conj_comp_eq {E F : Matrix k k ℝ} (hE : Eᵀ * E = 1) (hF : Fᵀ * F = 1) {x y : k → ℝ}
    (h : E * diagonal x * Eᵀ = F * diagonal y * Fᵀ) (φ : ℝ → ℝ) :
    E * diagonal (fun i => φ (x i)) * Eᵀ = F * diagonal (fun i => φ (y i)) * Fᵀ := by
  have h0 := sq_norm_conj_sub hE hF x y
  rw [h, sub_self, norm_zero, zero_pow two_ne_zero] at h0
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => by positivity).1 h0.symm
  have h2 : ∀ i j, (Eᵀ * F) i j ^ 2 * (x i - y j) ^ 2 = 0 := fun i j =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).1 (h1 i (Finset.mem_univ _)) j
      (Finset.mem_univ _)
  have h3 := sq_norm_conj_sub hE hF (fun i => φ (x i)) (fun i => φ (y i))
  have h4 : ‖E * diagonal (fun i => φ (x i)) * Eᵀ - F * diagonal (fun i => φ (y i)) * Fᵀ‖ ^ 2 =
      0 := by
    rw [h3]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rcases mul_eq_zero.1 (h2 i j) with h5 | h5
    · rw [h5, zero_mul]
    · have h6 : x i = y j := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h5)
      rw [h6]
      simp
  have h5 : ‖E * diagonal (fun i => φ (x i)) * Eᵀ - F * diagonal (fun i => φ (y i)) * Fᵀ‖ = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 h4
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

/-- Lipschitz functions act as Lipschitz maps on symmetric matrices in the Frobenius norm.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem norm_conj_comp_sub_le {E F : Matrix k k ℝ} (hE : Eᵀ * E = 1) (hF : Fᵀ * F = 1)
    (x y : k → ℝ) {φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ u v, |φ u - φ v| ≤ C * |u - v|) :
    ‖E * diagonal (fun i => φ (x i)) * Eᵀ - F * diagonal (fun i => φ (y i)) * Fᵀ‖ ≤
      C * ‖E * diagonal x * Eᵀ - F * diagonal y * Fᵀ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) two_ne_zero).1 ?_
  rw [mul_pow, sq_norm_conj_sub hE hF, sq_norm_conj_sub hE hF, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← mul_pow]
  refine sq_le_sq.2 ((hφ _ _).trans_eq ?_)
  rw [abs_mul, abs_of_nonneg hC]

/-- `tr (E X Eᵀ F Y Fᵀ) = ∑ᵢⱼ (Eᵀ F)ᵢⱼ² xᵢ yⱼ`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem trace_conj_mul_conj (E F : Matrix k k ℝ) (x y : k → ℝ) :
    trace (E * diagonal x * Eᵀ * (F * diagonal y * Fᵀ)) =
      ∑ i, ∑ j, (Eᵀ * F) i j ^ 2 * (x i * y j) := by
  have h1 : E * diagonal x * Eᵀ * (F * diagonal y * Fᵀ) =
      E * (diagonal x * (Eᵀ * F) * diagonal y * Fᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : diagonal x * (Eᵀ * F) * diagonal y * Fᵀ * E =
      diagonal x * (Eᵀ * F) * diagonal y * (Eᵀ * F)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h2, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply (M := diagonal x * (Eᵀ * F) * diagonal y),
    transpose_apply, mul_diagonal, diagonal_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `det (Q diag(m) Qᵀ) = ∏ m` for orthogonal `Q`. -/
lemma det_conj {Q : Matrix k k ℝ} (hQ : Qᵀ * Q = 1) (m : k → ℝ) :
    (Q * diagonal m * Qᵀ).det = ∏ i, m i := by
  have h1 : Q.det * Q.det = 1 := by
    have h := congrArg Matrix.det hQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  linear_combination (∏ i, m i) * h1

/-- A real square matrix that does not increase the Euclidean norm. -/
def IsContr (T : Matrix k k ℝ) : Prop := ∀ x : k → ℝ, (T *ᵥ x) ⬝ᵥ (T *ᵥ x) ≤ x ⬝ᵥ x

omit [DecidableEq k] in
lemma IsContr.mul {A B : Matrix k k ℝ} (hA : IsContr A) (hB : IsContr B) : IsContr (A * B) :=
  fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (hA _).trans (hB x)

lemma isContr_of_orth {Q : Matrix k k ℝ} (hQ : Qᵀ * Q = 1) : IsContr Q := fun x => by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mulVec_transpose,
    hQ, Matrix.transpose_one, Matrix.one_mulVec]

lemma isContr_diagonal {w : k → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ 1) :
    IsContr (diagonal w) := fun x => by
  simp only [Matrix.mulVec_diagonal, dotProduct]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : w i * w i ≤ 1 := by nlinarith [hw i, hw0 i]
  nlinarith [mul_self_nonneg (x i)]

/-- The eigenvalues of `T Tᵀ` lie in `(0, 1]` if `Tᵀ` is a contraction and `T` is invertible.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem exists_eig_mul_transpose {T : Matrix k k ℝ} (hT : IsContr Tᵀ) (hdet : T.det ≠ 0) :
    ∃ (Q : Matrix k k ℝ) (m : k → ℝ), Qᵀ * Q = 1 ∧ T * Tᵀ = Q * diagonal m * Qᵀ ∧
      (∀ i, 0 < m i) ∧ ∀ i, m i ≤ 1 := by
  have hsym : (T * Tᵀ)ᵀ = T * Tᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  obtain ⟨Q, m, hQ, hA⟩ := exists_eig hsym
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ
  have hC : (Qᵀ * T) * (Qᵀ * T)ᵀ = diagonal m := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Qᵀ * T * (Tᵀ * Q) = Qᵀ * (T * Tᵀ) * Q := by simp only [Matrix.mul_assoc]
      _ = (Qᵀ * Q) * diagonal m * (Qᵀ * Q) := by rw [hA]; simp only [Matrix.mul_assoc]
      _ = diagonal m := by rw [hQ, Matrix.one_mul, Matrix.mul_one]
  have hm : ∀ i, m i = ∑ j, (Qᵀ * T) i j ^ 2 := fun i => by
    have h := congrFun (congrFun hC i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    simp only [transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => (sq _).symm
  have hne : ∀ i, m i ≠ 0 := by
    have h1 : ∏ i, m i ≠ 0 := by
      rw [← det_conj hQ m, ← hA, Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero hdet hdet
    exact fun i => Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  have hnn : ∀ i, 0 ≤ m i := fun i => by
    rw [hm]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨Q, m, hQ, hA, fun i => lt_of_le_of_ne (hnn i) (hne i).symm, fun i => ?_⟩
  have h1 := hT fun a => Q a i
  have h2 : (fun a => Q a i) ⬝ᵥ (fun a => Q a i) = 1 := by
    have h := congrFun (congrFun hQ i) i
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h
    simpa [dotProduct] using h
  have h3 : ∀ j, (Tᵀ *ᵥ fun a => Q a i) j = (Qᵀ * T) i j := fun j => by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, transpose_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [h2] at h1
  rw [hm]
  simp only [dotProduct, h3] at h1
  simpa [sq] using h1

end Spectral

/-! ### The smoothed log-determinant -/

section Model

variable {d₁ d₂ : ℕ} {ε : ℝ}

/-- The rectangular diagonal matrix `dg(v)` of Appendix A of arXiv 2511.04485. -/
def dg (s : ℕ → ℝ) : Matrix (Fin d₁) (Fin d₂) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then s i else 0

lemma singularDiag_eq_dg (W : Matrix (Fin d₁) (Fin d₂) ℝ) : singularDiag W = dg (sv W) := rfl

lemma diagonal_mul_dg (x s : ℕ → ℝ) :
    diagonal (fun i : Fin d₁ => x i) * (dg s : Matrix (Fin d₁) (Fin d₂) ℝ) =
      dg fun n => x n * s n := by
  ext i j
  simp only [diagonal_mul, dg, of_apply]
  split_ifs <;> simp

lemma dg_mul_diagonal (s x : ℕ → ℝ) :
    (dg s : Matrix (Fin d₁) (Fin d₂) ℝ) * diagonal (fun j : Fin d₂ => x j) =
      dg fun n => s n * x n := by
  ext i j
  simp only [mul_diagonal, dg, of_apply]
  split_ifs with h
  · rw [h]
  · simp

lemma transpose_dg (s : ℕ → ℝ) :
    (dg s : Matrix (Fin d₁) (Fin d₂) ℝ)ᵀ = dg s := by
  ext j i
  simp only [transpose_apply, dg, of_apply]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · simp [h, Ne.symm h]

lemma transpose_dg_mul_dg {s : ℕ → ℝ} (hs : ∀ j, d₁ ≤ j → s j = 0) (t : ℕ → ℝ) :
    (dg s : Matrix (Fin d₁) (Fin d₂) ℝ)ᵀ * (dg t : Matrix (Fin d₁) (Fin d₂) ℝ) =
      diagonal fun j : Fin d₂ => s j * t j := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [transpose_apply, dg, of_apply, diagonal_apply]
  by_cases hj : (j : ℕ) < d₁
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin d₁)]
    · simp only [↓reduceIte]
      by_cases hjj : j = j'
      · subst hjj; simp
      · have : (j : ℕ) ≠ j' := fun e => hjj (Fin.ext e)
        simp [hjj, this]
    · intro i _ hi
      have : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
      simp [this]
    · simp
  · have h0 : s j = 0 := hs j (not_lt.1 hj)
    rw [Finset.sum_eq_zero]
    · by_cases hjj : j = j'
      · subst hjj
        simp [h0]
      · simp [hjj]
    · intro i _
      have : (i : ℕ) ≠ j := fun e => hj (e ▸ i.2)
      simp [this]

lemma sv_eq_zero_of_right (W : Matrix (Fin d₁) (Fin d₂) ℝ) {i : ℕ} (h : d₂ ≤ i) : sv W i = 0 :=
  LinearMap.singularValues_of_finrank_le _ (by simpa using h)

lemma sv_transpose (W : Matrix (Fin d₁) (Fin d₂) ℝ) (i : ℕ) : sv Wᵀ i = sv W i :=
  LeanDLRA.SVD.singularValues_transpose W i

lemma sv_eq_zero_of_left (W : Matrix (Fin d₁) (Fin d₂) ℝ) {i : ℕ} (h : d₁ ≤ i) : sv W i = 0 := by
  rw [← sv_transpose]
  exact sv_eq_zero_of_right Wᵀ h

lemma sv_eq_zero_of_min (W : Matrix (Fin d₁) (Fin d₂) ℝ) {i : ℕ} (h : min d₁ d₂ ≤ i) :
    sv W i = 0 := by
  rcases min_le_iff.1 h with h | h
  · exact sv_eq_zero_of_left W h
  · exact sv_eq_zero_of_right W h

variable {W Y : Matrix (Fin d₁) (Fin d₂) ℝ} {U : Matrix (Fin d₁) (Fin d₁) ℝ}
  {V : Matrix (Fin d₂) (Fin d₂) ℝ}

/-- `Wᵀ W = V diag(σ²) Vᵀ`. -/
lemma isSVD_transpose_mul_self (h : IsSVD W U V) :
    Wᵀ * W = V * diagonal (fun j : Fin d₂ => sv W j ^ 2) * Vᵀ := by
  have e := h.eq
  rw [singularDiag_eq_dg] at e
  set D : Matrix (Fin d₁) (Fin d₂) ℝ := dg (sv W) with hD
  have h1 : Dᵀ * D = diagonal fun j : Fin d₂ => sv W j ^ 2 := by
    rw [hD, transpose_dg_mul_dg (s := sv W) (fun j hj => sv_eq_zero_of_left W hj)]
    simp only [sq]
  calc Wᵀ * W = (U * D * Vᵀ)ᵀ * (U * D * Vᵀ) := by rw [← e]
    _ = V * Dᵀ * (Uᵀ * U) * D * Vᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by rw [h.left, Matrix.mul_one, Matrix.mul_assoc V, h1]

/-- `W Wᵀ = U diag(σ²) Uᵀ`. -/
lemma isSVD_mul_transpose_self (h : IsSVD W U V) :
    W * Wᵀ = U * diagonal (fun i : Fin d₁ => sv W i ^ 2) * Uᵀ := by
  have h1 := isSVD_transpose_mul_self h.transpose
  simpa only [Matrix.transpose_transpose, sv_transpose] using h1

/-- The `ε`-smoothed log-determinant `F_ε(W) = ∑ᵢ f_ε(σᵢ(W))` of eq. (1) of arXiv 2511.04485, the
sum running over the `min(d₁, d₂)` singular values. -/
def FEps (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  ∑ i ∈ Finset.range (min d₁ d₂), fEps ε (sv W i)

lemma FEps_eq_sum_right (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W = ∑ j : Fin d₂, fEps ε (sv W j) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => fEps ε (sv W i)) d₂, FEps]
  refine Finset.sum_subset (Finset.range_subset_range.2 (min_le_right _ _)) fun x _ hx => ?_
  rw [sv_eq_zero_of_min W (not_lt.1 (Finset.mem_range.not.1 hx)), fEps_zero hε]

lemma FEps_transpose (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : FEps ε Wᵀ = FEps ε W := by
  simp only [FEps, sv_transpose, min_comm d₂ d₁]

/-- The variational upper bound: for orthogonal `Q` and `m ∈ (0, 1]^{d₂}`, with
`M = Q diag(m) Qᵀ`, `F_ε(Y) ≤ ½ tr(Y M Yᵀ) - ½ ε² log det M`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem FEps_le_trace (hε : 0 < ε) (Y : Matrix (Fin d₁) (Fin d₂) ℝ)
    {Q : Matrix (Fin d₂) (Fin d₂) ℝ} (hQ : Qᵀ * Q = 1) {m : Fin d₂ → ℝ} (hm0 : ∀ k, 0 < m k)
    (hm1 : ∀ k, m k ≤ 1) :
    FEps ε Y ≤
      1 / 2 * trace (Y * (Q * diagonal m * Qᵀ) * Yᵀ) - ε ^ 2 / 2 * ∑ k, Real.log (m k) := by
  obtain ⟨U, V, h⟩ := exists_isSVD Y
  have hC := orth_mul h.right hQ
  have hC' := orth_mul' h.right hQ
  set C := Vᵀ * Q with hCdef
  have hT : trace (Y * (Q * diagonal m * Qᵀ) * Yᵀ) =
      ∑ j, ∑ k, C j k ^ 2 * (sv Y j ^ 2 * m k) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, isSVD_transpose_mul_self h]
    exact trace_conj_mul_conj V Q _ _
  have hL : ∑ k, Real.log (m k) = ∑ j, ∑ k, C j k ^ 2 * Real.log (m k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, sum_sq_col hC, one_mul]
  have hF : FEps ε Y = ∑ j, ∑ k, C j k ^ 2 * fEps ε (sv Y j) := by
    rw [FEps_eq_sum_right hε]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, sum_sq_row hC', one_mul]
  rw [hT, hL, hF, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 := fEps_le hε (sv_nonneg Y j) (hm0 k) (hm1 k)
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (C j k))
  calc C j k ^ 2 * fEps ε (sv Y j) ≤ _ := h2
    _ = _ := by ring

/-- The bound `FEps_le_trace` is attained at `M = V diag(max (σⱼ / ε, 1)⁻²) Vᵀ`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem FEps_eq_trace (hε : 0 < ε) (h : IsSVD Y U V) :
    FEps ε Y =
      1 / 2 * trace (Y * (V * diagonal (fun j : Fin d₂ => (dEps ε (sv Y j) ^ 2)⁻¹) * Vᵀ) * Yᵀ) +
        ε ^ 2 * ∑ j : Fin d₂, Real.log (dEps ε (sv Y j)) := by
  have hT : trace (Y * (V * diagonal (fun j : Fin d₂ => (dEps ε (sv Y j) ^ 2)⁻¹) * Vᵀ) * Yᵀ) =
      ∑ j : Fin d₂, sv Y j ^ 2 * (dEps ε (sv Y j) ^ 2)⁻¹ := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, isSVD_transpose_mul_self h, trace_conj_mul_conj,
      h.right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Matrix.one_apply_ne (Ne.symm hk)]
    · simp
  rw [hT, FEps_eq_sum_right hε, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fEps_eq hε]
  ring

/-- Multiplication by a contraction: if `aᵀ` is a contraction and `a` is invertible, then
`F_ε(Y) ≤ F_ε(Y a) - ε² log |det a|`.  (Recall that `Real.log` is even, so that `Real.log a.det` is
`log |det a|`.)
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem FEps_le_FEps_mul (hε : 0 < ε) (Y : Matrix (Fin d₁) (Fin d₂) ℝ)
    {a : Matrix (Fin d₂) (Fin d₂) ℝ} (ha : IsContr aᵀ) (hdet : a.det ≠ 0) :
    FEps ε Y ≤ FEps ε (Y * a) - ε ^ 2 * Real.log a.det := by
  obtain ⟨U, V, h⟩ := exists_isSVD (Y * a)
  set w : Fin d₂ → ℝ := fun j => (dEps ε (sv (Y * a) j))⁻¹ with hw
  have hw0 : ∀ j, 0 < w j := fun j => inv_pos.2 dEps_pos
  have hw1 : ∀ j, w j ≤ 1 := fun j => inv_le_one_of_one_le₀ one_le_dEps
  set T : Matrix (Fin d₂) (Fin d₂) ℝ := a * (V * diagonal w) with hT
  have hVt : Vᵀ * Vᵀᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact h.right
  have hVt' : Vᵀᵀ * Vᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp h.right
  have hTt : IsContr Tᵀ := by
    rw [hT, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
    exact (isContr_diagonal (fun j => (hw0 j).le) hw1).mul ((isContr_of_orth hVt').mul ha)
  have hdetV : V.det ^ 2 = 1 := by
    have h1 := congrArg Matrix.det h.right
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    rw [sq, h1]
  have hdetV0 : V.det ≠ 0 := fun e => by simp [e] at hdetV
  have hdetw : (∏ j, w j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (hw0 j).ne'
  have hdetT : T.det = a.det * (V.det * ∏ j, w j) := by
    rw [hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdetT0 : T.det ≠ 0 := by
    rw [hdetT]
    exact mul_ne_zero hdet (mul_ne_zero hdetV0 hdetw)
  obtain ⟨Q, m, hQ, hTT, hm0, hm1⟩ := exists_eig_mul_transpose hTt hdetT0
  have h1 := FEps_le_trace hε Y hQ hm0 hm1
  have h2 := FEps_eq_trace hε h
  have hN : Q * diagonal m * Qᵀ =
      a * (V * diagonal (fun j : Fin d₂ => (dEps ε (sv (Y * a) j) ^ 2)⁻¹) * Vᵀ) * aᵀ := by
    rw [← hTT, hT]
    have h3 : diagonal w * diagonal w =
        diagonal fun j : Fin d₂ => (dEps ε (sv (Y * a) j) ^ 2)⁻¹ := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext j
      simp only [hw]
      rw [← mul_inv, sq]
    rw [← h3, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  have hL : ∑ k, Real.log (m k) =
      2 * Real.log a.det - 2 * ∑ j : Fin d₂, Real.log (dEps ε (sv (Y * a) j)) := by
    have h3 : ∏ k, m k = T.det ^ 2 := by
      rw [← det_conj hQ m, ← hTT, Matrix.det_mul, Matrix.det_transpose, sq]
    have h4 : ∑ k, Real.log (m k) = Real.log (∏ k, m k) :=
      (Real.log_prod fun k _ => (hm0 k).ne').symm
    have h5 : Real.log V.det = 0 := by
      have h6 := congrArg Real.log hdetV
      rw [Real.log_pow, Real.log_one] at h6
      simpa using h6
    have h7 : Real.log (∏ j, w j) = -∑ j : Fin d₂, Real.log (dEps ε (sv (Y * a) j)) := by
      rw [Real.log_prod fun j _ => (hw0 j).ne', ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => Real.log_inv _
    rw [h4, h3, Real.log_pow, hdetT, Real.log_mul hdet (mul_ne_zero hdetV0 hdetw),
      Real.log_mul hdetV0 hdetw, h5, h7]
    push_cast
    ring
  have hTr : trace (Y * (a * (V * diagonal (fun j : Fin d₂ => (dEps ε (sv (Y * a) j) ^ 2)⁻¹) *
      Vᵀ) * aᵀ) * Yᵀ) = trace (Y * a * (V * diagonal (fun j : Fin d₂ =>
        (dEps ε (sv (Y * a) j) ^ 2)⁻¹) * Vᵀ) * (Y * a)ᵀ) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hN, hTr, hL] at h1
  rw [h2] at *
  nlinarith

end Model

/-! ### The reweighting operator -/

section Reweight

variable {d d₁ d₂ : ℕ} {ε : ℝ}

/-- The matrix `E Σ_{ε,d}⁻¹ Eᵀ` of Definition 4.1 of arXiv 2511.04485, where
`Σ_{ε,d} = diag(max (sᵢ / ε, 1))_{i < d}`. -/
def weightMat (ε : ℝ) (E : Matrix (Fin d) (Fin d) ℝ) (s : ℕ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  E * diagonal (fun i : Fin d => (dEps ε (s i))⁻¹) * Eᵀ

/-- The symmetric square root of `weightMat`. -/
def rootMat (ε : ℝ) (E : Matrix (Fin d) (Fin d) ℝ) (s : ℕ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  E * diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹) * Eᵀ

lemma weightMat_transpose (E : Matrix (Fin d) (Fin d) ℝ) (s : ℕ → ℝ) :
    (weightMat ε E s)ᵀ = weightMat ε E s := by
  simp only [weightMat, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma rootMat_transpose (E : Matrix (Fin d) (Fin d) ℝ) (s : ℕ → ℝ) :
    (rootMat ε E s)ᵀ = rootMat ε E s := by
  simp only [rootMat, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma rootMat_mul_rootMat {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1) (s : ℕ → ℝ) :
    rootMat ε E s * rootMat ε E s = weightMat ε E s := by
  have h1 : diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹) *
      diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹) =
      diagonal fun i : Fin d => (dEps ε (s i))⁻¹ := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (inv_nonneg.2 dEps_pos.le)
  calc rootMat ε E s * rootMat ε E s =
      E * (diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹) * (Eᵀ * E) *
        diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹)) * Eᵀ := by
        simp only [rootMat, Matrix.mul_assoc]
    _ = _ := by rw [hE, Matrix.mul_one, h1, weightMat]

lemma isContr_rootMat {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1) (s : ℕ → ℝ) :
    IsContr (rootMat ε E s) := by
  have hE' : Eᵀᵀ * Eᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hE
  have h1 : IsContr (E * (diagonal (fun i : Fin d => √(dEps ε (s i))⁻¹) * Eᵀ)) :=
    (isContr_of_orth hE).mul
      ((isContr_diagonal (fun _ => Real.sqrt_nonneg _) fun i =>
        Real.sqrt_le_one.2 (inv_le_one_of_one_le₀ one_le_dEps)).mul (isContr_of_orth hE'))
  rwa [rootMat, Matrix.mul_assoc]

lemma log_det_rootMat {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1) (s : ℕ → ℝ) :
    Real.log (rootMat ε E s).det = -(1 / 2) * ∑ i : Fin d, Real.log (dEps ε (s i)) := by
  have hpos : ∀ i : Fin d, 0 < √(dEps ε (s i))⁻¹ := fun i =>
    Real.sqrt_pos.2 (inv_pos.2 dEps_pos)
  rw [rootMat, det_conj hE, Real.log_prod fun i _ => (hpos i).ne', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_sqrt (inv_pos.2 dEps_pos).le, Real.log_inv]
  ring

lemma det_rootMat_ne_zero {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1) (s : ℕ → ℝ) :
    (rootMat ε E s).det ≠ 0 := by
  rw [rootMat, det_conj hE]
  exact Finset.prod_ne_zero_iff.2 fun i _ => (Real.sqrt_pos.2 (inv_pos.2 dEps_pos)).ne'

variable {W W' : Matrix (Fin d₁) (Fin d₂) ℝ} {U U' : Matrix (Fin d₁) (Fin d₁) ℝ}
  {V V' : Matrix (Fin d₂) (Fin d₂) ℝ}

/-- The left weight of an SVD does not depend on the SVD. -/
lemma weightMat_left_congr (h : IsSVD W' U V) (h' : IsSVD W' U' V') :
    weightMat ε U (sv W') = weightMat ε U' (sv W') := by
  have h1 := conj_comp_eq h.left h'.left
    ((isSVD_mul_transpose_self h).symm.trans (isSVD_mul_transpose_self h'))
    fun t => (dEps ε √t)⁻¹
  simpa only [weightMat, Real.sqrt_sq (sv_nonneg W' _)] using h1

/-- The right weight of an SVD does not depend on the SVD. -/
lemma weightMat_right_congr (h : IsSVD W' U V) (h' : IsSVD W' U' V') :
    weightMat ε V (sv W') = weightMat ε V' (sv W') := by
  have h1 := conj_comp_eq h.right h'.right
    ((isSVD_transpose_mul_self h).symm.trans (isSVD_transpose_mul_self h'))
    fun t => (dEps ε √t)⁻¹
  simpa only [weightMat, Real.sqrt_sq (sv_nonneg W' _)] using h1

/-- **Definition 4.1** of arXiv 2511.04485 for given SVD factors:
`W ↦ U Σ_{ε,d₁}⁻¹ Uᵀ W V Σ_{ε,d₂}⁻¹ Vᵀ`. -/
def reweightOf (ε : ℝ) (U : Matrix (Fin d₁) (Fin d₁) ℝ) (V : Matrix (Fin d₂) (Fin d₂) ℝ)
    (s : ℕ → ℝ) : Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ :=
  (Frobenius.leftMulCLM (weightMat ε U s)).comp (Frobenius.rightMulCLM (weightMat ε V s))

lemma reweightOf_apply (U : Matrix (Fin d₁) (Fin d₁) ℝ) (V : Matrix (Fin d₂) (Fin d₂) ℝ)
    (s : ℕ → ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweightOf ε U V s W = weightMat ε U s * W * weightMat ε V s := by
  simp [reweightOf, Matrix.mul_assoc]

/-- A fixed full SVD of `W`, left factor. -/
def svdU (W : Matrix (Fin d₁) (Fin d₂) ℝ) : Matrix (Fin d₁) (Fin d₁) ℝ :=
  (exists_isSVD W).choose

/-- A fixed full SVD of `W`, right factor. -/
def svdV (W : Matrix (Fin d₁) (Fin d₂) ℝ) : Matrix (Fin d₂) (Fin d₂) ℝ :=
  (exists_isSVD W).choose_spec.choose

lemma isSVD_svd (W : Matrix (Fin d₁) (Fin d₂) ℝ) : IsSVD W (svdU W) (svdV W) :=
  (exists_isSVD W).choose_spec.choose_spec

/-- The reweighting operator `R_{W',ε}` of **Definition 4.1** of arXiv 2511.04485.  By
`reweight_eq` it does not depend on the SVD used. -/
def reweight (ε : ℝ) (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ :=
  reweightOf ε (svdU W') (svdV W') (sv W')

/-- **Definition 4.1** of arXiv 2511.04485: `R_{W',ε}` may be computed from any full SVD
`W' = U dg(σ(W')) Vᵀ`.  The paper leaves this independence implicit. -/
theorem reweight_eq (h : IsSVD W' U V) : reweight ε W' = reweightOf ε U V (sv W') := by
  rw [reweight, reweightOf, reweightOf, weightMat_left_congr h (isSVD_svd W'),
    weightMat_right_congr h (isSVD_svd W')]

lemma reweight_apply (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W' W = weightMat ε U (sv W') * W * weightMat ε V (sv W') := by
  rw [reweight_eq h, reweightOf_apply]

/-- `R_{W',ε}` is self-adjoint for the Frobenius inner product (used in Lemma 4.1 of
arXiv 2511.04485). -/
theorem reweight_symm (ε : ℝ) (W' A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪reweight ε W' A, B⟫ = ⟪A, reweight ε W' B⟫ := by
  rw [reweight_apply (isSVD_svd W'), reweight_apply (isSVD_svd W'), Frobenius.inner_mul_right,
    Frobenius.inner_mul_left, weightMat_transpose, weightMat_transpose, Matrix.mul_assoc]

/-- `⟪W, R_{W',ε}(W)⟫ = ‖R^{1/2} W‖²`, with the symmetric square roots of the two weights. -/
lemma inner_reweight_self (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪W, reweight ε W' W⟫ = ‖rootMat ε U (sv W') * W * rootMat ε V (sv W')‖ ^ 2 := by
  rw [reweight_apply h, ← real_inner_self_eq_norm_sq, ← rootMat_mul_rootMat h.left,
    ← rootMat_mul_rootMat h.right, Frobenius.inner_mul_right, Frobenius.inner_mul_left,
    rootMat_transpose, rootMat_transpose]
  simp only [Matrix.mul_assoc]

/-- The sum `∑ log max (σᵢ / ε, 1)` over the left index set equals the one over the right index
set. -/
lemma sum_log_left_eq_right (hε : 0 < ε) (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∑ i : Fin d₁, Real.log (dEps ε (sv W' i)) = ∑ j : Fin d₂, Real.log (dEps ε (sv W' j)) := by
  have key : ∀ d, min d₁ d₂ ≤ d → ∑ i : Fin d, Real.log (dEps ε (sv W' i)) =
      ∑ i ∈ Finset.range (min d₁ d₂), Real.log (dEps ε (sv W' i)) := fun d hd => by
    rw [Fin.sum_univ_eq_sum_range (fun i => Real.log (dEps ε (sv W' i))) d]
    refine (Finset.sum_subset (Finset.range_subset_range.2 hd) fun x _ hx => ?_).symm
    rw [sv_eq_zero_of_min W' (not_lt.1 (Finset.mem_range.not.1 hx)),
      dEps_of_le hε hε.le, Real.log_one]
  rw [key d₁ (min_le_left _ _), key d₂ (min_le_right _ _)]

/-- `R_{W,ε}(W) = U dg(σᵢ / max (σᵢ / ε, 1)²) Vᵀ` (the computation in Lemma A.4 of
arXiv 2511.04485). -/
theorem reweight_self (h : IsSVD W U V) :
    reweight ε W W =
      U * (dg (fun n => sv W n / dEps ε (sv W n) ^ 2) : Matrix (Fin d₁) (Fin d₂) ℝ) * Vᵀ := by
  have e := h.eq
  rw [singularDiag_eq_dg] at e
  rw [reweight_apply h]
  set w : ℕ → ℝ := fun n => (dEps ε (sv W n))⁻¹ with hw
  set D : Matrix (Fin d₁) (Fin d₂) ℝ := dg (sv W) with hD
  have h1 : diagonal (fun i : Fin d₁ => w i) * D * diagonal (fun j : Fin d₂ => w j) =
      dg fun n => sv W n / dEps ε (sv W n) ^ 2 := by
    rw [hD, diagonal_mul_dg, dg_mul_diagonal]
    congr 1
    ext n
    simp only [hw]
    rw [div_eq_mul_inv, sq, mul_inv]
    ring
  calc weightMat ε U (sv W) * W * weightMat ε V (sv W)
      = U * diagonal (fun i : Fin d₁ => w i) * Uᵀ * (U * D * Vᵀ) *
          (V * diagonal (fun j : Fin d₂ => w j) * Vᵀ) := by
        rw [← e]
        rfl
    _ = U * (diagonal (fun i : Fin d₁ => w i) * (Uᵀ * U) * D * (Vᵀ * V) *
          diagonal (fun j : Fin d₂ => w j)) * Vᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h.left, h.right, Matrix.mul_one, Matrix.mul_one, h1]

/-- `R_{W,ε}(W) = W N`, with `N = V diag(max (σⱼ / ε, 1)⁻²) Vᵀ`. -/
lemma reweight_self_eq_mul (h : IsSVD W U V) :
    reweight ε W W = W * (V * diagonal (fun j : Fin d₂ => (dEps ε (sv W j) ^ 2)⁻¹) * Vᵀ) := by
  have e := h.eq
  rw [singularDiag_eq_dg] at e
  rw [reweight_self h]
  set N : Matrix (Fin d₂) (Fin d₂) ℝ := diagonal fun j : Fin d₂ => (dEps ε (sv W j) ^ 2)⁻¹ with hN
  set D : Matrix (Fin d₁) (Fin d₂) ℝ := dg (sv W) with hD
  have h1 : (dg (fun n => sv W n / dEps ε (sv W n) ^ 2) : Matrix (Fin d₁) (Fin d₂) ℝ) = D * N := by
    rw [hN, hD, dg_mul_diagonal (sv W) fun n => (dEps ε (sv W n) ^ 2)⁻¹]
    simp only [div_eq_mul_inv]
  rw [h1]
  calc U * (D * N) * Vᵀ = U * D * (Vᵀ * V) * N * Vᵀ := by
        rw [h.right, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = (U * D * Vᵀ) * (V * N * Vᵀ) := by simp only [Matrix.mul_assoc]
    _ = W * (V * N * Vᵀ) := by rw [← e]

/-- `F_ε(W') = ½ ⟪W', R_{W',ε}(W')⟫ + ε² ∑ᵢ log max (σᵢ / ε, 1)`. -/
lemma FEps_eq_inner (hε : 0 < ε) (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W' = 1 / 2 * ⟪W', reweight ε W' W'⟫ +
      ε ^ 2 * ∑ j : Fin d₂, Real.log (dEps ε (sv W' j)) := by
  have h := isSVD_svd W'
  rw [FEps_eq_trace hε h, reweight_self_eq_mul h, Frobenius.inner_eq_trace]
  congr 2
  exact Matrix.trace_mul_comm _ _

/-- The quadratic model `Q_ε(W | W') = F_ε(W') + ½ ⟪W, R(W)⟫ - ½ ⟪W', R(W')⟫` of eq. (2) of
arXiv 2511.04485. -/
def quadModel (ε : ℝ) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  FEps ε W' + 1 / 2 * ⟪W, reweight ε W' W⟫ - 1 / 2 * ⟪W', reweight ε W' W'⟫

/-- **The majorization** `F_ε(W) ≤ Q_ε(W | W')` for all `W`, `W'`, stated in Section 4.1 of
arXiv 2511.04485 and left unproved there (footnote 2: "beyond the scope of this paper, we believe
that the statement is true").  The proof combines the variational bound `FEps_le_trace`, its
attainment `FEps_eq_trace` and the multiplicativity of the determinant, see
`FEps_le_FEps_mul`. -/
theorem FEps_le_quadModel (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W ≤ quadModel ε W' W := by
  have h := isSVD_svd W'
  set U := svdU W'
  set V := svdV W'
  set a₁ := rootMat ε U (sv W') with ha₁
  set a₂ := rootMat ε V (sv W') with ha₂
  have hc₁ : IsContr a₁ := isContr_rootMat h.left _
  have hc₂ : IsContr a₂ := isContr_rootMat h.right _
  have ht₁ : a₁ᵀ = a₁ := rootMat_transpose _ _
  have ht₂ : a₂ᵀ = a₂ := rootMat_transpose _ _
  have hd₁ : a₁.det ≠ 0 := det_rootMat_ne_zero h.left _
  have hd₂ : a₂.det ≠ 0 := det_rootMat_ne_zero h.right _
  have h1 := FEps_le_FEps_mul hε W (a := a₂) (by rwa [ht₂]) hd₂
  have h2 := FEps_le_FEps_mul hε (W * a₂)ᵀ (a := a₁) (by rwa [ht₁]) hd₁
  rw [FEps_transpose] at h2
  have h3 : (W * a₂)ᵀ * a₁ = (a₁ * W * a₂)ᵀ := by
    simp only [Matrix.transpose_mul, ht₁, ht₂, Matrix.mul_assoc]
  rw [h3, FEps_transpose] at h2
  have h4 := FEps_le_trace hε (a₁ * W * a₂) (Q := 1) (m := fun _ => 1)
    (by simp) (fun _ => one_pos) (fun _ => le_rfl)
  have h5 : (1 : Matrix (Fin d₂) (Fin d₂) ℝ) * diagonal (fun _ => (1 : ℝ)) * 1ᵀ = 1 := by simp
  have h5' : Matrix.trace (a₁ * W * a₂ * (a₁ * W * a₂)ᵀ) = ⟪W, reweight ε W' W⟫ := by
    rw [inner_reweight_self h, ← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace,
      Matrix.trace_mul_comm]
  rw [h5, Matrix.mul_one, h5'] at h4
  simp only [Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero] at h4
  have h6 := FEps_eq_inner hε W'
  have h7 : Real.log a₂.det = -(1 / 2) * ∑ j : Fin d₂, Real.log (dEps ε (sv W' j)) :=
    log_det_rootMat h.right _
  have h8 : Real.log a₁.det = -(1 / 2) * ∑ j : Fin d₂, Real.log (dEps ε (sv W' j)) := by
    rw [ha₁, log_det_rootMat h.left, sum_log_left_eq_right hε]
  rw [h7] at h1
  rw [h8] at h2
  rw [quadModel, h6]
  nlinarith

/-- The quadratic form of `R_{W',ε}` in the singular bases:
`⟪W, R(W)⟫ = ∑ᵢⱼ wᵢ wⱼ Zᵢⱼ²`, `Z = Uᵀ W V`, `wᵢ = max (σᵢ / ε, 1)⁻¹`. -/
lemma inner_reweight_eq_sum (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪W, reweight ε W' W⟫ = ∑ i : Fin d₁, ∑ j : Fin d₂,
      (dEps ε (sv W' i))⁻¹ * (dEps ε (sv W' j))⁻¹ * (Uᵀ * W * V) i j ^ 2 := by
  rw [reweight_apply h]
  set D₁ : Matrix (Fin d₁) (Fin d₁) ℝ := diagonal fun i : Fin d₁ => (dEps ε (sv W' i))⁻¹ with hD₁
  set D₂ : Matrix (Fin d₂) (Fin d₂) ℝ := diagonal fun j : Fin d₂ => (dEps ε (sv W' j))⁻¹ with hD₂
  have h1 : weightMat ε U (sv W') * W * weightMat ε V (sv W') =
      U * (D₁ * (Uᵀ * W * V) * D₂ * Vᵀ) := by
    simp only [weightMat, hD₁, hD₂, Matrix.mul_assoc]
  rw [h1, Frobenius.inner_mul_left', Frobenius.inner_mul_right', Matrix.transpose_transpose,
    Frobenius.inner_def]
  simp only [hD₁, hD₂, mul_diagonal, diagonal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `R_{W',ε} ≤ I`. -/
lemma inner_reweight_self_le (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪W, reweight ε W' W⟫ ≤ ‖W‖ ^ 2 := by
  have hUt : Uᵀᵀ * Uᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp h.left
  have hVt : Vᵀᵀ * Vᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp h.right
  have hZ : ‖Uᵀ * W * V‖ = ‖W‖ := by
    have h1 : ‖Uᵀ * W * Vᵀᵀ‖ = ‖Uᵀ * W‖ := Frobenius.norm_mul_transpose_of_orthonormal hVt _
    rw [Matrix.transpose_transpose] at h1
    rw [h1, Frobenius.norm_mul_of_orthonormal hUt]
  rw [inner_reweight_eq_sum h, ← hZ, Frobenius.norm_sq_eq_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : (dEps ε (sv W' i))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_dEps
  have h2 : (dEps ε (sv W' j))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le_dEps
  have h3 : 0 ≤ (dEps ε (sv W' i))⁻¹ := (inv_pos.2 dEps_pos).le
  have h4 : 0 ≤ (dEps ε (sv W' j))⁻¹ := (inv_pos.2 dEps_pos).le
  have h5 : (dEps ε (sv W' i))⁻¹ * (dEps ε (sv W' j))⁻¹ ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (sq_nonneg _) h5

lemma dEps_mono (hε : 0 < ε) {σ τ : ℝ} (h : σ ≤ τ) : dEps ε σ ≤ dEps ε τ :=
  max_le_max (div_le_div_of_nonneg_right h hε.le) le_rfl

/-- **Lemma 4.1.1** of arXiv 2511.04485, quantitative form as in its proof:
`⟪W, R_{W',ε}(W)⟫ ≥ max (σ₁(W') / ε, 1)⁻² ‖W‖²`. -/
theorem le_inner_reweight (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    (dEps ε (sv W' 0))⁻¹ ^ 2 * ‖W‖ ^ 2 ≤ ⟪W, reweight ε W' W⟫ := by
  have h := isSVD_svd W'
  set U := svdU W'
  set V := svdV W'
  have hUt : Uᵀᵀ * Uᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp h.left
  have hVt : Vᵀᵀ * Vᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp h.right
  have hZ : ‖Uᵀ * W * V‖ = ‖W‖ := by
    have h1 : ‖Uᵀ * W * Vᵀᵀ‖ = ‖Uᵀ * W‖ := Frobenius.norm_mul_transpose_of_orthonormal hVt _
    rw [Matrix.transpose_transpose] at h1
    rw [h1, Frobenius.norm_mul_of_orthonormal hUt]
  rw [inner_reweight_eq_sum h, ← hZ, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hmono : ∀ n : ℕ, (dEps ε (sv W' 0))⁻¹ ≤ (dEps ε (sv W' n))⁻¹ := fun n =>
    inv_anti₀ dEps_pos (dEps_mono hε ((Matrix.toEuclideanLin W').singularValues_antitone
      (Nat.zero_le n)))
  have h0 : 0 ≤ (dEps ε (sv W' 0))⁻¹ := (inv_pos.2 dEps_pos).le
  have h1 := hmono i
  have h2 := hmono j
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [sq]
  exact mul_le_mul h1 h2 h0 (h0.trans h1)

/-- **Lemma 4.1.1** of arXiv 2511.04485: `R_{W',ε}` is positive definite. -/
theorem reweight_pos (hε : 0 < ε) (W' : Matrix (Fin d₁) (Fin d₂) ℝ)
    {W : Matrix (Fin d₁) (Fin d₂) ℝ} (hW : W ≠ 0) : 0 < ⟪W, reweight ε W' W⟫ := by
  refine lt_of_lt_of_le ?_ (le_inner_reweight hε W' W)
  have h1 : 0 < (dEps ε (sv W' 0))⁻¹ := inv_pos.2 dEps_pos
  have h2 : 0 < ‖W‖ := norm_pos_iff.2 hW
  positivity

/-- **Eq. (2)/(5)** of arXiv 2511.04485 with `R_{W',ε}(W')` in place of the gradient; see
`quadModel_eq` for Lemma 4.1.3. -/
lemma quadModel_eq_aux (ε : ℝ) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    quadModel ε W' W = FEps ε W' + ⟪reweight ε W' W', W - W'⟫ +
      1 / 2 * ⟪W - W', reweight ε W' (W - W')⟫ := by
  have h1 : ⟪W', reweight ε W' W⟫ = ⟪reweight ε W' W', W⟫ := (reweight_symm ε W' W' W).symm
  have h2 : ⟪W, reweight ε W' W'⟫ = ⟪reweight ε W' W', W⟫ := real_inner_comm _ _
  have h3 := real_inner_comm (reweight ε W' W') W'
  rw [quadModel, map_sub, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right, h1, h2]
  linarith

/-- The descent inequality for `F_ε`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem FEps_le_add_inner (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W ≤ FEps ε W' + ⟪reweight ε W' W', W - W'⟫ + 1 / 2 * ‖W - W'‖ ^ 2 := by
  have h1 := FEps_le_quadModel hε W' W
  have h2 := inner_reweight_self_le (ε := ε) (isSVD_svd W') (W - W')
  rw [quadModel_eq_aux] at h1
  linarith

/-- `(R_{W,ε}(W))ᵀ = R_{Wᵀ,ε}(Wᵀ)`. -/
lemma transpose_reweight_self (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    (reweight ε W W)ᵀ = reweight ε Wᵀ Wᵀ := by
  have h := isSVD_svd W
  rw [reweight_self h, reweight_self h.transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, transpose_dg, sv_transpose,
    Matrix.mul_assoc]

end Reweight

/-! ### The Jordan-Wielandt dilation and the Lipschitz gradient -/

section Dilation

variable {d₁ d₂ : ℕ} {ε : ℝ}

/-- The Jordan-Wielandt dilation `[[0, W], [Wᵀ, 0]]`. -/
def dil (W : Matrix (Fin d₁) (Fin d₂) ℝ) : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ :=
  fromBlocks 0 W Wᵀ 0

lemma dil_transpose (W : Matrix (Fin d₁) (Fin d₂) ℝ) : (dil W)ᵀ = dil W := by
  simp [dil, fromBlocks_transpose]

lemma dil_sub (A B : Matrix (Fin d₁) (Fin d₂) ℝ) : dil A - dil B = dil (A - B) := by
  ext (i | i) (j | j) <;> simp [dil]

lemma sq_norm_dil (W : Matrix (Fin d₁) (Fin d₂) ℝ) : ‖dil W‖ ^ 2 = 2 * ‖W‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, dil, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, transpose_apply]
  have h : ∑ j : Fin d₂, ∑ i : Fin d₁, W i j ^ 2 = ∑ i : Fin d₁, ∑ j : Fin d₂, W i j ^ 2 :=
    Finset.sum_comm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    zero_add, add_zero]
  rw [h]
  ring

/-- Functions of the square of the dilation of `W` are block diagonal in the SVD of `W`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem exists_dil_eig (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∃ (E : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ) (a : Fin d₁ ⊕ Fin d₂ → ℝ),
      Eᵀ * E = 1 ∧ dil W = E * diagonal a * Eᵀ ∧ ∀ φ : ℝ → ℝ,
        E * diagonal (fun k => φ (a k ^ 2)) * Eᵀ =
          fromBlocks (svdU W * diagonal (fun i : Fin d₁ => φ (sv W i ^ 2)) * (svdU W)ᵀ) 0 0
            (svdV W * diagonal (fun j : Fin d₂ => φ (sv W j ^ 2)) * (svdV W)ᵀ) := by
  obtain ⟨E, a, hE, hA⟩ := exists_eig (dil_transpose W)
  refine ⟨E, a, hE, hA, fun φ => ?_⟩
  have h := isSVD_svd W
  set U := svdU W
  set V := svdV W
  set D : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ := fromBlocks U 0 0 V with hD
  have hDt : Dᵀ * D = 1 := by
    rw [hD, fromBlocks_transpose, fromBlocks_multiply]
    simp [h.left, h.right]
  set l : Fin d₁ ⊕ Fin d₂ → ℝ := Sum.elim (fun i => sv W i ^ 2) (fun j => sv W j ^ 2) with hl
  have hblock : ∀ φ : ℝ → ℝ, D * diagonal (fun k => φ (l k)) * Dᵀ =
      fromBlocks (U * diagonal (fun i : Fin d₁ => φ (sv W i ^ 2)) * Uᵀ) 0 0
        (V * diagonal (fun j : Fin d₂ => φ (sv W j ^ 2)) * Vᵀ) := fun φ => by
    have h1 : (diagonal fun k => φ (l k)) =
        fromBlocks (diagonal fun i : Fin d₁ => φ (sv W i ^ 2)) 0 0
          (diagonal fun j : Fin d₂ => φ (sv W j ^ 2)) := by
      rw [fromBlocks_diagonal]
      congr 1
      ext k
      rcases k with k | k <;> simp [hl]
    rw [h1, hD, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hsq : dil W * dil W = D * diagonal (fun k => id (l k)) * Dᵀ := by
    rw [hblock id, dil, fromBlocks_multiply]
    simp only [id, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [isSVD_mul_transpose_self h, isSVD_transpose_mul_self h]
  have hE' : E * diagonal (fun k => a k ^ 2) * Eᵀ = D * diagonal (fun k => id (l k)) * Dᵀ := by
    rw [← hsq]
    conv_rhs => rw [hA]
    have h2 : diagonal a * diagonal a = diagonal fun k => a k ^ 2 := by
      rw [Matrix.diagonal_mul_diagonal]
      simp only [sq]
    calc E * diagonal (fun k => a k ^ 2) * Eᵀ = E * (diagonal a * (Eᵀ * E) * diagonal a) * Eᵀ := by
          rw [hE, Matrix.mul_one, h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hq := conj_comp_eq hE hDt hE' φ
  simp only [id] at hq
  rw [hq, hblock φ]

/-- The function `φ` of the dilation of `W` is the dilation of `R_{W,ε}(W)`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem exists_dil_eq (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∃ (E : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ) (a : Fin d₁ ⊕ Fin d₂ → ℝ),
      Eᵀ * E = 1 ∧ dil W = E * diagonal a * Eᵀ ∧
        dil (reweight ε W W) = E * diagonal (fun k => phiEps ε (a k)) * Eᵀ := by
  obtain ⟨E, a, hE, hA, hφ'⟩ := exists_dil_eig W
  refine ⟨E, a, hE, hA, ?_⟩
  have h := isSVD_svd W
  have hq := hφ' (qEps ε)
  have hqs : ∀ n, qEps ε (sv W n ^ 2) = (dEps ε (sv W n) ^ 2)⁻¹ := fun n => by
    rw [qEps, Real.sqrt_sq (sv_nonneg W n)]
  simp only [hqs] at hq
  have hφ : E * diagonal (fun k => phiEps ε (a k)) * Eᵀ =
      dil W * (E * diagonal (fun k => qEps ε (a k ^ 2)) * Eᵀ) := by
    have h2 : diagonal a * diagonal (fun k => qEps ε (a k ^ 2)) =
        diagonal fun k => phiEps ε (a k) := by
      rw [Matrix.diagonal_mul_diagonal]
      rfl
    conv_rhs => rw [hA]
    calc E * diagonal (fun k => phiEps ε (a k)) * Eᵀ =
        E * (diagonal a * (Eᵀ * E) * diagonal (fun k => qEps ε (a k ^ 2))) * Eᵀ := by
          rw [hE, Matrix.mul_one, h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  have h3 := reweight_self_eq_mul (ε := ε) h
  have h4 := reweight_self_eq_mul (ε := ε) h.transpose
  rw [← transpose_reweight_self] at h4
  simp only [sv_transpose] at h4
  have hW : ∀ (A : Matrix (Fin d₁) (Fin d₁) ℝ) (B : Matrix (Fin d₂) (Fin d₂) ℝ),
      dil W * fromBlocks A 0 0 B = fromBlocks 0 (W * B) (Wᵀ * A) 0 := fun A B => by
    simp [dil, fromBlocks_multiply]
  rw [hφ, hq, hW, ← h3, ← h4]
  rfl

/-- **Lemma A.2** of arXiv 2511.04485, the `1`-Lipschitz part (claimed there without proof), for the
explicit gradient `R_{W,ε}(W)`.  The proof applies `norm_conj_comp_sub_le` to the
Jordan-Wielandt dilations. -/
theorem norm_reweight_self_sub_le (hε : 0 < ε) (W₁ W₂ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ‖reweight ε W₁ W₁ - reweight ε W₂ W₂‖ ≤ ‖W₁ - W₂‖ := by
  obtain ⟨E, a, hE, h1, h2⟩ := exists_dil_eq (ε := ε) W₁
  obtain ⟨F, b, hF, h3, h4⟩ := exists_dil_eq (ε := ε) W₂
  have h5 := norm_conj_comp_sub_le hE hF a b zero_le_one
    (fun u v => by simpa using abs_phiEps_sub_le hε u v)
  rw [← h1, ← h2, ← h3, ← h4, dil_sub, dil_sub, one_mul] at h5
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  rw [sq_norm_dil, sq_norm_dil] at h6
  linarith

lemma abs_inv_dEps_sub_le (hε : 0 < ε) (u v : ℝ) :
    |(dEps ε u)⁻¹ - (dEps ε v)⁻¹| ≤ ε⁻¹ * |u - v| := by
  have hA : 1 ≤ dEps ε u := one_le_dEps
  have hB : 1 ≤ dEps ε v := one_le_dEps
  have hA0 : 0 < dEps ε u := dEps_pos
  have hB0 : 0 < dEps ε v := dEps_pos
  have h1 : (dEps ε u)⁻¹ - (dEps ε v)⁻¹ =
      (dEps ε v - dEps ε u) * ((dEps ε u)⁻¹ * (dEps ε v)⁻¹) := by
    field_simp
  have h2 : |(dEps ε u)⁻¹ * (dEps ε v)⁻¹| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    have h3 := inv_le_one_of_one_le₀ hA
    have h4 := inv_le_one_of_one_le₀ hB
    have h5 : 0 < (dEps ε v)⁻¹ := inv_pos.2 hB0
    have h6 : 0 < (dEps ε u)⁻¹ := inv_pos.2 hA0
    nlinarith
  have h3 : |dEps ε v - dEps ε u| ≤ ε⁻¹ * |u - v| := by
    have h4 : |dEps ε v - dEps ε u| ≤ |v / ε - u / ε| := abs_max_sub_max_le_abs _ _ _
    have h5 : v / ε - u / ε = ε⁻¹ * (v - u) := by
      field_simp
    rwa [h5, abs_mul, abs_of_pos (inv_pos.2 hε), abs_sub_comm v u] at h4
  rw [h1, abs_mul]
  calc _ ≤ ε⁻¹ * |u - v| * 1 :=
        mul_le_mul h3 h2 (abs_nonneg _) (mul_nonneg (inv_pos.2 hε).le (abs_nonneg _))
    _ = _ := mul_one _

lemma abs_inv_dEps_abs_sub_le (hε : 0 < ε) (x y : ℝ) :
    |(dEps ε (abs x))⁻¹ - (dEps ε (abs y))⁻¹| ≤ ε⁻¹ * |x - y| :=
  (abs_inv_dEps_sub_le hε _ _).trans
    (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (inv_pos.2 hε).le)

lemma sq_norm_fromBlocks_diag (A : Matrix (Fin d₁) (Fin d₁) ℝ) (B : Matrix (Fin d₂) (Fin d₂) ℝ) :
    ‖(fromBlocks A 0 0 B : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ)‖ ^ 2 =
      ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum,
    Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero, zero_add]

/-- The two weights of `R_{W,ε}` depend Lipschitz continuously on `W`. -/
lemma norm_weightMat_sub_le (hε : 0 < ε) (W₁ W₂ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ‖weightMat ε (svdU W₁) (sv W₁) - weightMat ε (svdU W₂) (sv W₂)‖ ^ 2 +
      ‖weightMat ε (svdV W₁) (sv W₁) - weightMat ε (svdV W₂) (sv W₂)‖ ^ 2 ≤
        2 * (ε⁻¹ * ‖W₁ - W₂‖) ^ 2 := by
  obtain ⟨E, a, hE, h1, h2⟩ := exists_dil_eig W₁
  obtain ⟨F, b, hF, h3, h4⟩ := exists_dil_eig W₂
  have h5 := norm_conj_comp_sub_le hE hF a b (φ := fun x => (dEps ε (abs x))⁻¹)
    (inv_pos.2 hε).le (abs_inv_dEps_abs_sub_le hε)
  have key : ∀ (W : Matrix (Fin d₁) (Fin d₂) ℝ) (G : Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ)
      (c : Fin d₁ ⊕ Fin d₂ → ℝ),
      (∀ φ : ℝ → ℝ, G * diagonal (fun k => φ (c k ^ 2)) * Gᵀ =
        fromBlocks (svdU W * diagonal (fun i : Fin d₁ => φ (sv W i ^ 2)) * (svdU W)ᵀ) 0 0
          (svdV W * diagonal (fun j : Fin d₂ => φ (sv W j ^ 2)) * (svdV W)ᵀ)) →
      G * diagonal (fun k => (dEps ε (abs (c k)))⁻¹) * Gᵀ =
        fromBlocks (weightMat ε (svdU W) (sv W)) 0 0 (weightMat ε (svdV W) (sv W)) := by
    intro W G c hG
    have hs : ∀ n, abs (sv W n) = sv W n := fun n => abs_of_nonneg (sv_nonneg W n)
    have h6 := hG fun t => (dEps ε √t)⁻¹
    simp only [Real.sqrt_sq_eq_abs, hs] at h6
    exact h6
  rw [key W₁ E a h2, key W₂ F b h4, ← h1, ← h3, dil_sub] at h5
  set A₁ := weightMat ε (svdU W₁) (sv W₁) with hA₁
  set A₂ := weightMat ε (svdU W₂) (sv W₂) with hA₂
  set B₁ := weightMat ε (svdV W₁) (sv W₁) with hB₁
  set B₂ := weightMat ε (svdV W₂) (sv W₂) with hB₂
  have h8 : (fromBlocks A₁ 0 0 B₁ - fromBlocks A₂ 0 0 B₂ :
      Matrix (Fin d₁ ⊕ Fin d₂) (Fin d₁ ⊕ Fin d₂) ℝ) = fromBlocks (A₁ - A₂) 0 0 (B₁ - B₂) := by
    ext (i | i) (j | j) <;> simp
  have h9 : ‖fromBlocks A₁ 0 0 B₁ - fromBlocks A₂ 0 0 B₂‖ ≤ ε⁻¹ * ‖dil (W₁ - W₂)‖ := h5
  have h10 := pow_le_pow_left₀ (norm_nonneg _) h9 2
  rw [h8, sq_norm_fromBlocks_diag, mul_pow, sq_norm_dil] at h10
  rw [mul_pow]
  linarith

/-- `W' ↦ R_{W',ε}(T)` is continuous.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem continuous_reweight (hε : 0 < ε) (T : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Continuous fun W' : Matrix (Fin d₁) (Fin d₂) ℝ => reweight ε W' T := by
  have hbound : ∀ W₁ W₂ : Matrix (Fin d₁) (Fin d₂) ℝ,
      ‖weightMat ε (svdU W₁) (sv W₁) - weightMat ε (svdU W₂) (sv W₂)‖ ≤ 2 * ε⁻¹ * ‖W₁ - W₂‖ ∧
      ‖weightMat ε (svdV W₁) (sv W₁) - weightMat ε (svdV W₂) (sv W₂)‖ ≤ 2 * ε⁻¹ * ‖W₁ - W₂‖ := by
    intro W₁ W₂
    have h1 := norm_weightMat_sub_le hε W₁ W₂
    have h2 : 0 ≤ ε⁻¹ * ‖W₁ - W₂‖ := mul_nonneg (inv_pos.2 hε).le (norm_nonneg _)
    have h3 : 2 * (ε⁻¹ * ‖W₁ - W₂‖) ^ 2 ≤ (2 * ε⁻¹ * ‖W₁ - W₂‖) ^ 2 := by
      nlinarith [sq_nonneg (ε⁻¹ * ‖W₁ - W₂‖)]
    have h4 : 0 ≤ 2 * ε⁻¹ * ‖W₁ - W₂‖ := by nlinarith
    constructor
    · refine (pow_le_pow_iff_left₀ (norm_nonneg _) h4 two_ne_zero).1 ?_
      nlinarith [sq_nonneg ‖weightMat ε (svdV W₁) (sv W₁) - weightMat ε (svdV W₂) (sv W₂)‖]
    · refine (pow_le_pow_iff_left₀ (norm_nonneg _) h4 two_ne_zero).1 ?_
      nlinarith [sq_nonneg ‖weightMat ε (svdU W₁) (sv W₁) - weightMat ε (svdU W₂) (sv W₂)‖]
  have hL : Continuous fun W : Matrix (Fin d₁) (Fin d₂) ℝ => weightMat ε (svdU W) (sv W) :=
    (LipschitzWith.of_dist_le' fun W₁ W₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hbound W₁ W₂).1).continuous
  have hR : Continuous fun W : Matrix (Fin d₁) (Fin d₂) ℝ => weightMat ε (svdV W) (sv W) :=
    (LipschitzWith.of_dist_le' fun W₁ W₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hbound W₁ W₂).2).continuous
  have h1 : (fun W' : Matrix (Fin d₁) (Fin d₂) ℝ => reweight ε W' T) = fun W' =>
      Frobenius.mulCLM (Frobenius.mulCLM (weightMat ε (svdU W') (sv W')) T)
        (weightMat ε (svdV W') (sv W')) := by
    ext1 W'
    rw [reweight_apply (isSVD_svd W')]
    rfl
  rw [h1]
  exact ((Frobenius.mulCLM.continuous.comp
    ((Frobenius.mulCLM.continuous.comp hL).clm_apply continuous_const))).clm_apply hR

end Dilation

/-! ### Differentiability, the gradient and the quadratic model -/

section Gradient

variable {d₁ d₂ : ℕ} {ε : ℝ} {W : Matrix (Fin d₁) (Fin d₂) ℝ}
  {U : Matrix (Fin d₁) (Fin d₁) ℝ} {V : Matrix (Fin d₂) (Fin d₂) ℝ}

/-- A quadratic error bound gives a gradient. -/
lemma hasGradientAt_of_bound {f : Matrix (Fin d₁) (Fin d₂) ℝ → ℝ}
    {g x : Matrix (Fin d₁) (Fin d₂) ℝ} {C : ℝ}
    (hb : ∀ y, |f y - f x - ⟪g, y - x⟫| ≤ C * ‖y - x‖ ^ 2) : HasGradientAt f g x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hC : 0 < |C| + 1 := by positivity
  have hδ : 0 < c / (|C| + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs]
  have h1 : ‖y - x‖ < c / (|C| + 1) := by simpa [dist_eq_norm] using hy
  have h2 : (|C| + 1) * ‖y - x‖ ≤ c := by
    rw [lt_div_iff₀ hC] at h1
    linarith
  have h3 : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc |f y - f x - ⟪g, y - x⟫| ≤ C * ‖y - x‖ ^ 2 := hb y
    _ ≤ (|C| + 1) * ‖y - x‖ ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = (|C| + 1) * ‖y - x‖ * ‖y - x‖ := by ring
    _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- `F_ε` agrees with its linearization up to a quadratic error.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem abs_FEps_sub_le (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    |FEps ε W - FEps ε W' - ⟪reweight ε W' W', W - W'⟫| ≤ 3 / 2 * ‖W - W'‖ ^ 2 := by
  have h1 := FEps_le_add_inner hε W' W
  have h2 := FEps_le_add_inner hε W W'
  have h3 : ⟪reweight ε W W, W' - W⟫ = -⟪reweight ε W W, W - W'⟫ := by
    rw [← inner_neg_right, neg_sub]
  have h4 : |⟪reweight ε W W - reweight ε W' W', W - W'⟫| ≤ ‖W - W'‖ ^ 2 := by
    calc _ ≤ ‖reweight ε W W - reweight ε W' W'‖ * ‖W - W'‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖W - W'‖ * ‖W - W'‖ :=
        mul_le_mul_of_nonneg_right (norm_reweight_self_sub_le hε W W') (norm_nonneg _)
      _ = _ := (sq _).symm
  rw [inner_sub_left] at h4
  have h4' := abs_le.1 h4
  have h5 : ‖W' - W‖ = ‖W - W'‖ := norm_sub_rev _ _
  rw [h3, h5] at h2
  have h6 : 0 ≤ ‖W - W'‖ ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- **Lemma A.2** of arXiv 2511.04485: `F_ε` is differentiable, with gradient `R_{W,ε}(W)`.  The
explicit formula is `gradient_FEps`.  The paper quotes the Lewis-Sendov theorem on spectral
functions; here the result follows from the majorization and the Lipschitz estimate. -/
theorem hasGradientAt_FEps (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    HasGradientAt (FEps ε) (reweight ε W W) W :=
  hasGradientAt_of_bound (C := 3 / 2) fun y => abs_FEps_sub_le hε W y

/-- **Lemma A.4** of arXiv 2511.04485, eq. (13): `R_{W,ε}(W) = ∇F_ε(W)`. -/
theorem reweight_self_eq_gradient (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W W = gradient (FEps ε) W :=
  (hasGradientAt_FEps hε W).gradient.symm

/-- **Lemma A.2** of arXiv 2511.04485, eq. (10): for every full SVD `W = U dg(σ) Vᵀ`,
`∇F_ε(W) = U dg(σᵢ / max (σᵢ / ε, 1)²) Vᵀ`. -/
theorem gradient_FEps (hε : 0 < ε) (h : IsSVD W U V) :
    gradient (FEps ε) W =
      U * (dg (fun i => sv W i / max (sv W i / ε) 1 ^ 2) : Matrix (Fin d₁) (Fin d₂) ℝ) * Vᵀ := by
  rw [← reweight_self_eq_gradient hε, reweight_self h]
  rfl

/-- **Lemma A.2** of arXiv 2511.04485: `F_ε` is differentiable. -/
theorem differentiable_FEps (hε : 0 < ε) : Differentiable ℝ (FEps ε :
    Matrix (Fin d₁) (Fin d₂) ℝ → ℝ) := fun W =>
  (hasGradientAt_FEps hε W).hasFDerivAt.differentiableAt

/-- **Lemma A.2** of arXiv 2511.04485: `∇F_ε` is `1`-Lipschitz for the Frobenius norm.  The paper
states this without proof. -/
theorem lipschitzWith_gradient_FEps (hε : 0 < ε) :
    LipschitzWith 1 (gradient (FEps ε) : Matrix (Fin d₁) (Fin d₂) ℝ → Matrix (Fin d₁) (Fin d₂) ℝ) :=
  LipschitzWith.mk_one fun W₁ W₂ => by
    rw [← reweight_self_eq_gradient hε, ← reweight_self_eq_gradient hε, dist_eq_norm, dist_eq_norm]
    exact norm_reweight_self_sub_le hε W₁ W₂

/-- **Lemma 4.1.3** of arXiv 2511.04485, eq. (5):
`Q_ε(W | W') = F_ε(W') + ⟪∇F_ε(W'), W - W'⟫ + ½ ⟪W - W', R_{W',ε}(W - W')⟫`. -/
theorem quadModel_eq (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    quadModel ε W' W = FEps ε W' + ⟪gradient (FEps ε) W', W - W'⟫ +
      1 / 2 * ⟪W - W', reweight ε W' (W - W')⟫ := by
  rw [← reweight_self_eq_gradient hε, quadModel_eq_aux]

/-- The regularizer `Q3R_{W',ε}(W) = ½ ⟪W, R_{W',ε}(W)⟫` of eq. (6) of arXiv 2511.04485. -/
def Q3R (ε : ℝ) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ := 1 / 2 * ⟪W, reweight ε W' W⟫

lemma inner_reweight_nonneg (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 ≤ ⟪W, reweight ε W' W⟫ := by
  rw [inner_reweight_self (isSVD_svd W')]
  positivity

/-- Proof of Lemma 4.1.1 of arXiv 2511.04485: `Q3R_{W',ε}` is non-negative. -/
theorem Q3R_nonneg (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) : 0 ≤ Q3R ε W' W :=
  mul_nonneg (by norm_num) (inner_reweight_nonneg W' W)

/-- Proof of Lemma 4.1.1 of arXiv 2511.04485: `Q3R_{W',ε}(W) = 0` if and only if `W = 0`. -/
theorem Q3R_eq_zero_iff (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Q3R ε W' W = 0 ↔ W = 0 := by
  constructor
  · intro h
    by_contra hW
    have h1 := reweight_pos hε W' hW
    rw [Q3R] at h
    linarith
  · rintro rfl
    simp [Q3R]

/-- Section 4.2 of arXiv 2511.04485: `∇_W Q3R_{W',ε}(W) = R_{W',ε}(W)`. -/
theorem hasGradientAt_Q3R (ε : ℝ) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    HasGradientAt (Q3R ε W') (reweight ε W' W) W := by
  refine hasGradientAt_of_bound (C := 1 / 2) fun y => ?_
  have h1 : Q3R ε W' y - Q3R ε W' W - ⟪reweight ε W' W, y - W⟫ =
      1 / 2 * ⟪y - W, reweight ε W' (y - W)⟫ := by
    have h2 : ⟪y, reweight ε W' W⟫ = ⟪reweight ε W' W, y⟫ := real_inner_comm _ _
    have h3 : ⟪W, reweight ε W' y⟫ = ⟪reweight ε W' W, y⟫ := (reweight_symm ε W' W y).symm
    have h4 : ⟪reweight ε W' W, W⟫ = ⟪W, reweight ε W' W⟫ := real_inner_comm _ _
    rw [Q3R, Q3R, map_sub, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right, h2,
      h3, h4]
    ring
  rw [h1, abs_of_nonneg (mul_nonneg (by norm_num) (inner_reweight_nonneg W' _))]
  exact mul_le_mul_of_nonneg_left (inner_reweight_self_le (isSVD_svd W') _) (by norm_num)

/-- Corollary of Lemma A.4 of arXiv 2511.04485: `∇ Q3R_{W,ε}(W) = ∇F_ε(W)`. -/
theorem gradient_Q3R_self (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    gradient (Q3R ε W) W = gradient (FEps ε) W := by
  rw [(hasGradientAt_Q3R ε W W).gradient, reweight_self_eq_gradient hε]

/-- Up to a constant, the quadratic model is `Q3R`: the difference quotient form of the
majorization, `F_ε(W) - F_ε(W') ≤ Q3R_{W',ε}(W) - Q3R_{W',ε}(W')`.  This is the
majorization-minimization principle behind arXiv 2511.04485: decreasing `Q3R_{W',ε}` from `W'`
decreases `F_ε`. -/
theorem mm_descent (hε : 0 < ε) (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W - FEps ε W' ≤ Q3R ε W' W - Q3R ε W' W' := by
  have h := FEps_le_quadModel hε W' W
  rw [quadModel] at h
  rw [Q3R, Q3R]
  linarith

end Gradient

/-! ### The four-block formula -/

section Blocks

variable {d d₁ d₂ r : ℕ} {ε : ℝ}

/-- The number `r(W, ε) = |{i : σᵢ(W) > ε}|` of eq. (3) of arXiv 2511.04485. -/
def rankEnv (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : ℕ :=
  ((Finset.range (min d₁ d₂)).filter fun i => ε < sv W i).card

lemma rankEnv_le_min (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : rankEnv ε W ≤ min d₁ d₂ :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

lemma rankEnv_le_left (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : rankEnv ε W ≤ d₁ :=
  (rankEnv_le_min ε W).trans (min_le_left _ _)

lemma rankEnv_le_right (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : rankEnv ε W ≤ d₂ :=
  (rankEnv_le_min ε W).trans (min_le_right _ _)

/-- Since the singular values decrease, the first `r(W, ε)` of them are exactly those above `ε`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem lt_rankEnv_iff (hε : 0 ≤ ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) (i : ℕ) :
    i < rankEnv ε W ↔ ε < sv W i := by
  have hanti := (Matrix.toEuclideanLin W).singularValues_antitone
  have hmem : ∀ j, j ∈ (Finset.range (min d₁ d₂)).filter (fun i => ε < sv W i) ↔ ε < sv W j :=
    fun j => by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      by_contra hj
      rw [sv_eq_zero_of_min W (not_lt.1 hj)] at h
      exact absurd h (not_lt.2 hε)
  constructor
  · intro hi
    by_contra hc
    have hsub : (Finset.range (min d₁ d₂)).filter (fun i => ε < sv W i) ⊆ Finset.range i :=
      fun j hj => by
        rw [Finset.mem_range]
        by_contra hji
        exact hc (lt_of_lt_of_le ((hmem j).1 hj) (hanti (not_lt.1 hji)))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    exact absurd hi (not_lt.2 h1)
  · intro hi
    have hsub : Finset.range (i + 1) ⊆
        (Finset.range (min d₁ d₂)).filter (fun i => ε < sv W i) := fun j hj => by
      rw [hmem]
      exact lt_of_lt_of_le hi (hanti (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    exact h1

/-- The splitting behind eq. (4) of arXiv 2511.04485:
`E Σ_{ε,d}⁻¹ Eᵀ = ε E_r Σ⁻¹ E_rᵀ + (I - E_r E_rᵀ)`. -/
lemma weightMat_eq_blocks (hε : 0 < ε) {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1)
    {s : ℕ → ℝ} (hr : r ≤ d) (hs : ∀ i : Fin d, (i : ℕ) < r ↔ ε < s i) :
    weightMat ε E s =
      ε • (topCols hr E * diagonal (fun i : Fin r => (s i)⁻¹) * (topCols hr E)ᵀ) +
        (1 - topCols hr E * (topCols hr E)ᵀ) := by
  have hE' : E * Eᵀ = 1 := mul_eq_one_comm.mp hE
  ext a b
  have h1 : (1 : Matrix (Fin d) (Fin d) ℝ) a b = ∑ i, E a i * E b i := by
    rw [← hE', Matrix.mul_apply]
    rfl
  have h2 : (topCols hr E * diagonal (fun i : Fin r => (s i)⁻¹) * (topCols hr E)ᵀ) a b =
      ∑ i : Fin d, if (i : ℕ) < r then E a i * (s i)⁻¹ * E b i else 0 := by
    rw [← sum_castLE hr (fun i : Fin d => E a i * (s i)⁻¹ * E b i), Matrix.mul_apply]
    simp [topCols, mul_diagonal]
  have h3 : (topCols hr E * (topCols hr E)ᵀ) a b =
      ∑ i : Fin d, if (i : ℕ) < r then E a i * E b i else 0 := by
    rw [← sum_castLE hr (fun i : Fin d => E a i * E b i), Matrix.mul_apply]
    simp [topCols]
  have h4 : weightMat ε E s a b = ∑ i, E a i * (dEps ε (s i))⁻¹ * E b i := by
    rw [weightMat, Matrix.mul_apply]
    simp only [transpose_apply, mul_diagonal]
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, h1, h2, h3, h4, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) < r
  · have h5 : ε < s i := (hs i).1 hi
    have h6 : 0 < s i := hε.trans h5
    simp only [hi, ↓reduceIte]
    rw [dEps_of_ge hε h5.le, inv_div]
    field_simp
    ring
  · have h5 : s i ≤ ε := not_lt.1 fun h => hi ((hs i).2 h)
    simp only [hi, ↓reduceIte]
    rw [dEps_of_le hε h5]
    simp

variable {W W' : Matrix (Fin d₁) (Fin d₂) ℝ} {U : Matrix (Fin d₁) (Fin d₁) ℝ}
  {V : Matrix (Fin d₂) (Fin d₂) ℝ}

/-- The matrix `Σ⁻¹ = diag(σᵢ⁻¹)_{i < r}` of eq. (4) of arXiv 2511.04485. -/
def sigmaInv (W' : Matrix (Fin d₁) (Fin d₂) ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  diagonal fun i : Fin r => (sv W' i)⁻¹

lemma smul_add_mul_smul_add {m n : Type*} [Fintype m] [Fintype n] (ε : ℝ) (X P : Matrix m m ℝ)
    (Y Q : Matrix n n ℝ) (W : Matrix m n ℝ) :
    (ε • X + P) * W * (ε • Y + Q) =
      ε ^ 2 • (X * W * Y) + ε • (X * W * Q) + ε • (P * W * Y) + P * W * Q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
    sq]
  abel

/-- Eq. (4) of arXiv 2511.04485 for any threshold index `r` with `σᵢ > ε ↔ i < r`. -/
theorem reweight_eq_blocks (hε : 0 < ε) (h : IsSVD W' U V) (hr₁ : r ≤ d₁) (hr₂ : r ≤ d₂)
    (hs : ∀ i : ℕ, i < r ↔ ε < sv W' i) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W' W =
      ε ^ 2 • (topCols hr₁ U * sigmaInv W' r * (topCols hr₁ U)ᵀ * W * topCols hr₂ V *
          sigmaInv W' r * (topCols hr₂ V)ᵀ) +
        ε • (topCols hr₁ U * sigmaInv W' r * (topCols hr₁ U)ᵀ * W *
          (1 - topCols hr₂ V * (topCols hr₂ V)ᵀ)) +
        ε • ((1 - topCols hr₁ U * (topCols hr₁ U)ᵀ) * W * topCols hr₂ V * sigmaInv W' r *
          (topCols hr₂ V)ᵀ) +
        (1 - topCols hr₁ U * (topCols hr₁ U)ᵀ) * W * (1 - topCols hr₂ V * (topCols hr₂ V)ᵀ) := by
  have hL : weightMat ε U (sv W') = ε • (topCols hr₁ U * sigmaInv W' r * (topCols hr₁ U)ᵀ) +
      (1 - topCols hr₁ U * (topCols hr₁ U)ᵀ) := weightMat_eq_blocks hε h.left hr₁ fun i => hs i
  have hM : weightMat ε V (sv W') = ε • (topCols hr₂ V * sigmaInv W' r * (topCols hr₂ V)ᵀ) +
      (1 - topCols hr₂ V * (topCols hr₂ V)ᵀ) := weightMat_eq_blocks hε h.right hr₂ fun i => hs i
  rw [reweight_apply h, hL, hM, smul_add_mul_smul_add]
  simp only [Matrix.mul_assoc]

/-- **Lemma 4.1.2** of arXiv 2511.04485, eq. (4), with `r = r(W', ε)`, `U`, `V` the leading
`r` columns of the SVD factors and `Σ = diag(σᵢ(W'))_{i < r}`.  In particular `R_{W',ε}` only needs
a partial SVD. -/
theorem reweight_eq_four_blocks (hε : 0 < ε) (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W' W =
      ε ^ 2 • (topCols (rankEnv_le_left ε W') U * sigmaInv W' (rankEnv ε W') *
          (topCols (rankEnv_le_left ε W') U)ᵀ * W * topCols (rankEnv_le_right ε W') V *
          sigmaInv W' (rankEnv ε W') * (topCols (rankEnv_le_right ε W') V)ᵀ) +
        ε • (topCols (rankEnv_le_left ε W') U * sigmaInv W' (rankEnv ε W') *
          (topCols (rankEnv_le_left ε W') U)ᵀ * W *
          (1 - topCols (rankEnv_le_right ε W') V * (topCols (rankEnv_le_right ε W') V)ᵀ)) +
        ε • ((1 - topCols (rankEnv_le_left ε W') U * (topCols (rankEnv_le_left ε W') U)ᵀ) * W *
          topCols (rankEnv_le_right ε W') V * sigmaInv W' (rankEnv ε W') *
          (topCols (rankEnv_le_right ε W') V)ᵀ) +
        (1 - topCols (rankEnv_le_left ε W') U * (topCols (rankEnv_le_left ε W') U)ᵀ) * W *
          (1 - topCols (rankEnv_le_right ε W') V * (topCols (rankEnv_le_right ε W') V)ᵀ) :=
  reweight_eq_blocks hε h _ _ (lt_rankEnv_iff hε.le W') W

/-- The projector `E_r E_rᵀ` commutes with `E Σ_{ε,d}⁻¹ Eᵀ`. -/
lemma topCols_comm_weightMat (hε : 0 < ε) {E : Matrix (Fin d) (Fin d) ℝ} (hE : Eᵀ * E = 1)
    {s : ℕ → ℝ} (hr : r ≤ d) (hs : ∀ i : Fin d, (i : ℕ) < r ↔ ε < s i) :
    topCols hr E * (topCols hr E)ᵀ * weightMat ε E s =
      weightMat ε E s * (topCols hr E * (topCols hr E)ᵀ) := by
  have hI := topCols_transpose_mul_self hr hE
  rw [weightMat_eq_blocks hε hE hr hs]
  set F := topCols hr E with hF
  set S : Matrix (Fin r) (Fin r) ℝ := diagonal fun i : Fin r => (s i)⁻¹ with hS
  have h1 : F * Fᵀ * (F * S * Fᵀ) = F * S * Fᵀ := by
    calc F * Fᵀ * (F * S * Fᵀ) = F * (Fᵀ * F) * S * Fᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hI, Matrix.mul_one]
  have h2 : F * S * Fᵀ * (F * Fᵀ) = F * S * Fᵀ := by
    calc F * S * Fᵀ * (F * Fᵀ) = F * S * (Fᵀ * F) * Fᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hI, Matrix.mul_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]

/-- **Lemma 4.1** of arXiv 2511.04485 (block structure): `R_{W',ε}` commutes with the left
projector `P = U Uᵀ`, `U` the leading `r` singular vectors of `W'`.  Together with
`reweight_rightProj` and `LeanDLRA.leftProj_rightProj_comm`, this says that `R_{W',ε}` is block
diagonal in the splitting `P W Q`, `P W (I - Q)`, `(I - P) W Q`, `(I - P) W (I - Q)`, and eq. (4)
gives its action on each block. -/
theorem reweight_leftProj (hε : 0 < ε) (h : IsSVD W' U V) (hr₁ : r ≤ d₁)
    (hs : ∀ i : ℕ, i < r ↔ ε < sv W' i) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W' (leftProj (topCols hr₁ U) W) = leftProj (topCols hr₁ U) (reweight ε W' W) := by
  have hc := topCols_comm_weightMat hε h.left hr₁ fun i : Fin d₁ => hs i
  simp only [reweight_apply h, leftProj_apply]
  calc weightMat ε U (sv W') * (topCols hr₁ U * (topCols hr₁ U)ᵀ * W) * weightMat ε V (sv W')
      = weightMat ε U (sv W') * (topCols hr₁ U * (topCols hr₁ U)ᵀ) * W *
          weightMat ε V (sv W') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hc]; simp only [Matrix.mul_assoc]

/-- **Lemma 4.1** of arXiv 2511.04485 (block structure): `R_{W',ε}` commutes with the right
projector `Q = V Vᵀ`. -/
theorem reweight_rightProj (hε : 0 < ε) (h : IsSVD W' U V) (hr₂ : r ≤ d₂)
    (hs : ∀ i : ℕ, i < r ↔ ε < sv W' i) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    reweight ε W' (rightProj (topCols hr₂ V) W) = rightProj (topCols hr₂ V) (reweight ε W' W) := by
  have hc := topCols_comm_weightMat hε h.right hr₂ fun i : Fin d₂ => hs i
  simp only [reweight_apply h, rightProj_apply']
  calc weightMat ε U (sv W') * (W * (topCols hr₂ V * (topCols hr₂ V)ᵀ)) * weightMat ε V (sv W')
      = weightMat ε U (sv W') * W * (topCols hr₂ V * (topCols hr₂ V)ᵀ *
          weightMat ε V (sv W')) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc]; simp only [Matrix.mul_assoc]

/-! ### The limit `ε → 0`: a misstatement of Section 4.1 -/

/-- `i < rank W ↔ σᵢ(W) > 0`. -/
lemma lt_rank_iff (W : Matrix (Fin d₁) (Fin d₂) ℝ) (i : ℕ) : i < W.rank ↔ 0 < sv W i := by
  rw [LeanDLRA.SVD.rank_eq_finrank_range]
  exact (Matrix.toEuclideanLin W).singularValues_pos_iff_lt_finrank_range.symm

lemma rank_le_left (W : Matrix (Fin d₁) (Fin d₂) ℝ) : W.rank ≤ d₁ := by
  simpa using Matrix.rank_le_card_height W

lemma rank_le_right (W : Matrix (Fin d₁) (Fin d₂) ℝ) : W.rank ≤ d₂ := by
  simpa using Matrix.rank_le_card_width W

/-- For small `ε`, the threshold index of `σᵢ > ε` is the rank. -/
lemma eventually_lt_rank_iff (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ i : ℕ, i < W'.rank ↔ ε < sv W' i := by
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range W'.rank, ε < sv W' i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have h2 : 0 < sv W' i := (lt_rank_iff W' i).1 (Finset.mem_range.1 hi)
    filter_upwards [Ioo_mem_nhdsGT h2] with ε hε using hε.2
  filter_upwards [h1, self_mem_nhdsWithin] with ε hε h0
  refine ⟨h0, fun i => ⟨fun hi => hε i (Finset.mem_range.2 hi), fun hi => ?_⟩⟩
  exact (lt_rank_iff W' i).2 (lt_trans h0 hi)

/-- **Corrected form of a claim in Section 4.1** of arXiv 2511.04485.  Let `U`, `V` be the singular
vectors of `W'` with positive singular values.  As `ε → 0`,
`R_{W',ε}(W) → (I - U Uᵀ) W (I - V Vᵀ)`. -/
theorem tendsto_reweight (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Tendsto (fun ε => reweight ε W' W) (𝓝[>] 0)
      (𝓝 ((1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W *
        (1 - topCols (rank_le_right W') V * (topCols (rank_le_right W') V)ᵀ))) := by
  set A := topCols (rank_le_left W') U * sigmaInv W' W'.rank * (topCols (rank_le_left W') U)ᵀ * W *
    topCols (rank_le_right W') V * sigmaInv W' W'.rank * (topCols (rank_le_right W') V)ᵀ
  set B := topCols (rank_le_left W') U * sigmaInv W' W'.rank * (topCols (rank_le_left W') U)ᵀ * W *
    (1 - topCols (rank_le_right W') V * (topCols (rank_le_right W') V)ᵀ)
  set C := (1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W *
    topCols (rank_le_right W') V * sigmaInv W' W'.rank * (topCols (rank_le_right W') V)ᵀ
  set D := (1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W *
    (1 - topCols (rank_le_right W') V * (topCols (rank_le_right W') V)ᵀ)
  have hc : Continuous fun ε : ℝ => ε ^ 2 • A + ε • B + ε • C + D := by fun_prop
  have h1 : Tendsto (fun ε : ℝ => ε ^ 2 • A + ε • B + ε • C + D) (𝓝[>] 0) (𝓝 D) := by
    have h2 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, add_zero,
      zero_add] at h2
    exact tendsto_nhdsWithin_of_tendsto_nhds h2
  refine h1.congr' ?_
  filter_upwards [eventually_lt_rank_iff W'] with ε hε
  exact (reweight_eq_blocks hε.1 h _ _ hε.2 W).symm

/-- `R_{W',ε}(W) → 0` as `ε → 0` exactly when `(I - U Uᵀ) W (I - V Vᵀ) = 0`, where `U`, `V` are the
singular vectors of `W'` with positive singular values.  This corrects the statement of
Section 4.1 of arXiv 2511.04485, see `not_tendsto_reweight_zero`. -/
theorem tendsto_reweight_zero_iff (h : IsSVD W' U V) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Tendsto (fun ε => reweight ε W' W) (𝓝[>] 0) (𝓝 0) ↔
      (1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W *
        (1 - topCols (rank_le_right W') V * (topCols (rank_le_right W') V)ᵀ) = 0 := by
  constructor
  · intro h1
    exact tendsto_nhds_unique (tendsto_reweight h W) h1
  · intro h1
    have h2 := tendsto_reweight h W
    rwa [h1] at h2

/-- **Counterexample to a claim in Section 4.1** of arXiv 2511.04485, for a fixed expansion point
`W'`: the paper says that `R_{W',ε}(W)` tends to `0` as `ε → 0` for matrices `W` whose column and
row spaces are orthogonal to the columns of `U` and `V`.  The opposite holds: by eq. (4) such a `W`
has weight one, and the limit is `W` itself, so that it is not `0` unless `W = 0`.  (The vanishing
limit concerns the complementary matrices, see `tendsto_reweight_zero_iff`.)  Such `W ≠ 0` exist
whenever `W'` does not have full rank, see `exists_orthogonal_ne_zero`.  For the paper's reading
with `ε` following (7), where `W'` changes too, see `not_tendsto_reweight_zero_seq`. -/
theorem not_tendsto_reweight_zero (h : IsSVD W' U V) {W : Matrix (Fin d₁) (Fin d₂) ℝ}
    (hU : (topCols (rank_le_left W') U)ᵀ * W = 0) (hV : W * topCols (rank_le_right W') V = 0)
    (hW : W ≠ 0) : ¬ Tendsto (fun ε => reweight ε W' W) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_reweight_zero_iff h]
  have h1 : (1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W *
      (1 - topCols (rank_le_right W') V * (topCols (rank_le_right W') V)ᵀ) = W := by
    have h2 : (1 - topCols (rank_le_left W') U * (topCols (rank_le_left W') U)ᵀ) * W = W := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_zero, sub_zero]
    rw [h2, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.zero_mul, sub_zero]
  rwa [h1]

/-- By eq. (4), `R_{W',ε}` is the identity on the matrices `W` whose column and row spaces are
orthogonal to the leading `r(W', ε)` left and right singular vectors `U`, `V` of `W'` (the `U`, `V`
of Definition 4.1), for every `W'` and every `ε > 0`.
Supporting result for arXiv 2511.04485, Section 4.1, not stated in the paper. -/
theorem reweight_eq_self_of_orthogonal (hε : 0 < ε) (h : IsSVD W' U V)
    {W : Matrix (Fin d₁) (Fin d₂) ℝ} (hU : (topCols (rankEnv_le_left ε W') U)ᵀ * W = 0)
    (hV : W * topCols (rankEnv_le_right ε W') V = 0) : reweight ε W' W = W := by
  rw [reweight_eq_four_blocks hε h W]
  set Ur := topCols (rankEnv_le_left ε W') U
  set Vr := topCols (rankEnv_le_right ε W') V
  set Si := sigmaInv W' (rankEnv ε W')
  have h1 : Ur * Si * Urᵀ * W = 0 := by rw [Matrix.mul_assoc, hU, Matrix.mul_zero]
  have h2 : (1 - Ur * Urᵀ) * W * Vr = 0 := by rw [Matrix.mul_assoc, hV, Matrix.mul_zero]
  have h3 : (1 - Ur * Urᵀ) * W * (1 - Vr * Vrᵀ) = W := by
    have h4 : (1 - Ur * Urᵀ) * W = W := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_zero, sub_zero]
    rw [h4, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.zero_mul, sub_zero]
  rw [h1, h2, h3]
  simp

/-- **Counterexample to the claim of Section 4.1** of arXiv 2511.04485 **along the dynamics (7)**:
there the expansion point `W'_k` and the smoothing parameter `ε_k` change together.  Whatever the
sequence `(W'_k, ε_k)`, `ε_k > 0`, if `W ≠ 0` is orthogonal in the sense of the paper to the leading
`r(W'_k, ε_k)` singular vectors of `W'_k` for every `k`, then `R_{W'_k,ε_k}(W) = W` for every `k`
(`reweight_eq_self_of_orthogonal`), so that it does not tend to `0`. -/
theorem not_tendsto_reweight_zero_seq {e : ℕ → ℝ} (he : ∀ k, 0 < e k)
    {Wk : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ} {Uk : ℕ → Matrix (Fin d₁) (Fin d₁) ℝ}
    {Vk : ℕ → Matrix (Fin d₂) (Fin d₂) ℝ} (h : ∀ k, IsSVD (Wk k) (Uk k) (Vk k))
    {W : Matrix (Fin d₁) (Fin d₂) ℝ}
    (hU : ∀ k, (topCols (rankEnv_le_left (e k) (Wk k)) (Uk k))ᵀ * W = 0)
    (hV : ∀ k, W * topCols (rankEnv_le_right (e k) (Wk k)) (Vk k) = 0) (hW : W ≠ 0) :
    ¬ Tendsto (fun k => reweight (e k) (Wk k) W) atTop (𝓝 0) := by
  have e1 : (fun k => reweight (e k) (Wk k) W) = fun _ => W :=
    funext fun k => reweight_eq_self_of_orthogonal (he k) (h k) (hU k) (hV k)
  rw [e1]
  intro h0
  exact hW (tendsto_nhds_unique tendsto_const_nhds h0)

/-- The hypotheses of `not_tendsto_reweight_zero` hold for some `W ≠ 0` whenever `W'` does not have
full rank.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem exists_orthogonal_ne_zero (h : IsSVD W' U V) (hr : W'.rank < min d₁ d₂) :
    ∃ W : Matrix (Fin d₁) (Fin d₂) ℝ, W ≠ 0 ∧ (topCols (rank_le_left W') U)ᵀ * W = 0 ∧
      W * topCols (rank_le_right W') V = 0 := by
  have hr₁ : W'.rank < d₁ := lt_of_lt_of_le hr (min_le_left _ _)
  have hr₂ : W'.rank < d₂ := lt_of_lt_of_le hr (min_le_right _ _)
  set a : Fin d₁ := ⟨W'.rank, hr₁⟩ with ha
  set b : Fin d₂ := ⟨W'.rank, hr₂⟩ with hb
  have hUU : ∀ i : Fin d₁, i ≠ a → ∑ x, U x i * U x a = 0 := fun i hi => by
    have h1 := congrFun (congrFun h.left i) a
    rw [Matrix.one_apply_ne hi, Matrix.mul_apply] at h1
    simpa using h1
  have hVV : ∀ j : Fin d₂, j ≠ b → ∑ y, V y b * V y j = 0 := fun j hj => by
    have h1 := congrFun (congrFun h.right b) j
    rw [Matrix.one_apply_ne (Ne.symm hj), Matrix.mul_apply] at h1
    simpa using h1
  refine ⟨Matrix.of fun x y => U x a * V y b, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun M : Matrix (Fin d₁) (Fin d₂) ℝ => ∑ x, ∑ y, M x y ^ 2) h0
    simp only [of_apply, Matrix.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul] at h1
    rw [sum_sq_col h.left, sum_sq_col h.right] at h1
    norm_num at h1
  · ext i y
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have hi : Fin.castLE (rank_le_left W') i ≠ a := fun e => by
      have h1 := congrArg Fin.val e
      simp only [Fin.val_castLE, ha] at h1
      exact absurd i.2 (by omega)
    have h1 := hUU _ hi
    calc ∑ x, (topCols (rank_le_left W') U)ᵀ i x * (Matrix.of fun x y => U x a * V y b) x y
        = (∑ x, U x (Fin.castLE (rank_le_left W') i) * U x a) * V y b := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [topCols, transpose_apply, submatrix_apply, id, of_apply]
          ring
      _ = 0 := by rw [h1, zero_mul]
  · ext x j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have hj : Fin.castLE (rank_le_right W') j ≠ b := fun e => by
      have h1 := congrArg Fin.val e
      simp only [Fin.val_castLE, hb] at h1
      exact absurd j.2 (by omega)
    have h1 := hVV _ hj
    calc ∑ y, (Matrix.of fun x y => U x a * V y b) x y * topCols (rank_le_right W') V y j
        = U x a * ∑ y, V y b * V y (Fin.castLE (rank_le_right W') j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          simp only [topCols, submatrix_apply, id, of_apply]
          ring
      _ = 0 := by rw [h1, mul_zero]

end Blocks

/-! ### Basic properties of `F_ε` -/

section Properties

variable {d₁ d₂ : ℕ} {ε : ℝ}

lemma fEps_nonneg (hε : 0 < ε) {σ : ℝ} : 0 ≤ fEps ε σ := by
  rw [fEps_eq hε]
  have h1 : 0 ≤ Real.log (dEps ε σ) := Real.log_nonneg one_le_dEps
  have h2 : 0 < dEps ε σ := dEps_pos
  positivity

/-- Section 4.1 of arXiv 2511.04485: `F_ε` is bounded below by `0`. -/
theorem FEps_nonneg (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : 0 ≤ FEps ε W :=
  Finset.sum_nonneg fun _ _ => fEps_nonneg hε

/-- `‖W‖_F² = ∑ⱼ σⱼ²`. -/
lemma sq_norm_eq_sum_sv (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ‖W‖ ^ 2 = ∑ j : Fin d₂, sv W j ^ 2 := by
  have h := isSVD_svd W
  rw [← real_inner_self_eq_norm_sq, Frobenius.inner_eq_trace, isSVD_transpose_mul_self h,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, h.right, Matrix.one_mul, Matrix.trace_diagonal]

/-- Appendix A.1 of arXiv 2511.04485: `F_ε(W) = ½ ‖W‖_F²` if `σ₁(W) ≤ ε`. -/
theorem FEps_eq_half_sq (hε : 0 < ε) {W : Matrix (Fin d₁) (Fin d₂) ℝ} (hW : sv W 0 ≤ ε) :
    FEps ε W = 1 / 2 * ‖W‖ ^ 2 := by
  rw [FEps_eq_sum_right hε, sq_norm_eq_sum_sv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : sv W j ≤ ε :=
    ((Matrix.toEuclideanLin W).singularValues_antitone (Nat.zero_le _)).trans hW
  rw [fEps_eq hε, dEps_of_le hε h1]
  simp

/-- `F_ε(W) ≤ ½ ‖W‖_F²` for all `W`, the case `W' = 0` of the majorization.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem FEps_le_half_sq (hε : 0 < ε) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    FEps ε W ≤ 1 / 2 * ‖W‖ ^ 2 := by
  rw [FEps_eq_sum_right hε, sq_norm_eq_sum_sv, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simpa using fEps_le (m := 1) hε (sv_nonneg W j) one_pos le_rfl

end Properties

/-! ### Algorithms 1 and 2 -/

section Algorithms

variable {d₁ d₂ : ℕ} {ε : ℝ}

/-- Eq. (7) and line 2 of Algorithm 1 of arXiv 2511.04485: `ε_new = min (ε_old, σ_{r+1}(W))`.  The
singular values are zero-based here, so that `σ_{r+1}(W)` is `sv W r`. -/
def updateEps (rT : ℕ) (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ := min ε (sv W rT)

/-- Algorithm 1: the smoothing parameter does not increase.
Algorithm 1 of arXiv 2511.04485. -/
theorem updateEps_le (rT : ℕ) (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    updateEps rT ε W ≤ ε := min_le_left _ _

/-- Algorithm 1: after the update, `ε ≤ σ_{r+1}(W)`.
Algorithm 1 of arXiv 2511.04485. -/
theorem updateEps_le_sv (rT : ℕ) (ε : ℝ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    updateEps rT ε W ≤ sv W rT := min_le_right _ _

/-- The update of Algorithm 1 keeps `ε` positive if and only if `rank W > r_target`.  This is
needed for the next reweighting operator, and it is implicit in arXiv 2511.04485. -/
theorem updateEps_pos_iff (rT : ℕ) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 < updateEps rT ε W ↔ 0 < ε ∧ rT < W.rank := by
  rw [updateEps, lt_min_iff, lt_rank_iff]

/-- The rank envelope grows as `ε` decreases.  In particular `r(W, ε_new) ≥ r(W, ε_old)` in
Algorithm 1, so that the truncation of its line 4 needs the leading `r(W, ε_new)` singular vectors,
and a partial SVD of the order `r(W, ε_old)` of line 1 may not be enough.
Algorithm 1 of arXiv 2511.04485. -/
theorem rankEnv_anti {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) (W : Matrix (Fin d₁) (Fin d₂) ℝ) :
    rankEnv ε₂ W ≤ rankEnv ε₁ W := by
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_le_of_lt h hi.2⟩

/-- Algorithm 1, line 3: if `σ_{r+1}(W) ≤ ε_old`, then the rank envelope `r(W, ε_new)` is at most
the target rank; this is the design goal `r_env ≈ r_target` of arXiv 2511.04485, Section 4.2. -/
theorem rankEnv_updateEps_le (rT : ℕ) {W : Matrix (Fin d₁) (Fin d₂) ℝ} (h : sv W rT ≤ ε) :
    rankEnv (updateEps rT ε W) W ≤ rT := by
  rw [updateEps, min_eq_right h]
  by_contra hc
  have h1 := (lt_rankEnv_iff (sv_nonneg W rT) W rT).1 (not_le.1 hc)
  exact lt_irrefl _ h1

/-- If, on the other hand, `σ_{r+1}(W) > ε_old`, then `ε` is not changed and the rank envelope of
Algorithm 1 exceeds the target rank.
Algorithm 1 of arXiv 2511.04485. -/
theorem lt_rankEnv_updateEps (rT : ℕ) {W : Matrix (Fin d₁) (Fin d₂) ℝ} (hε : 0 ≤ ε)
    (h : ε < sv W rT) : rT < rankEnv (updateEps rT ε W) W := by
  rw [updateEps, min_eq_left h.le]
  exact (lt_rankEnv_iff hε W rT).2 h

/-- The parameters of Algorithm 2 of arXiv 2511.04485: reweighting period `T`, Q3R parameter `lam`,
learning rate `α`, moment parameters `β₁`, `β₂`, the offset `δ`, the factor `η` and the target
rank `rT`. -/
structure AdamQ3RParams where
  /-- The reweighting period. -/
  T : ℕ
  /-- The target rank. -/
  rT : ℕ
  /-- The Q3R parameter `λ`. -/
  lam : ℝ
  /-- The learning rate. -/
  α : ℝ
  /-- The first moment parameter. -/
  β₁ : ℝ
  /-- The second moment parameter. -/
  β₂ : ℝ
  /-- The offset in the denominator. -/
  δ : ℝ
  /-- The overall step factor. -/
  η : ℝ

/-- The state of Algorithm 2 of arXiv 2511.04485: the iterate, the expansion point `center` and the
smoothing parameter of the current reweighting operator, and the two moments. -/
structure AdamQ3RState (d₁ d₂ : ℕ) where
  /-- The iterate `W_t`. -/
  W : Matrix (Fin d₁) (Fin d₂) ℝ
  /-- The expansion point of the current reweighting operator. -/
  center : Matrix (Fin d₁) (Fin d₂) ℝ
  /-- The smoothing parameter. -/
  eps : ℝ
  /-- The first moment `m_t`. -/
  m : Matrix (Fin d₁) (Fin d₂) ℝ
  /-- The second moment `v_t`. -/
  v : Matrix (Fin d₁) (Fin d₂) ℝ

/-- Lines 3-5 of Algorithm 2 of arXiv 2511.04485: every `T` iterations, re-expand at the current
iterate and update `ε` by Algorithm 1. -/
def reweightStep (p : AdamQ3RParams) (t : ℕ) (s : AdamQ3RState d₁ d₂) : AdamQ3RState d₁ d₂ :=
  if t % p.T = 0 then { s with center := s.W, eps := updateEps p.rT s.eps s.W } else s

/-- The adaptive direction `α m̂ / (√v̂ + δ)` of line 13 of Algorithm 2 of arXiv 2511.04485,
computed from the moments `m_{t+1}`, `v_{t+1}` by lines 10-11.  All operations are entrywise. -/
def adamDir (p : AdamQ3RParams) (t : ℕ) (m v : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  Matrix.of fun i j =>
    p.α * ((1 - p.β₁ ^ (t + 1))⁻¹ * m i j) / (√((1 - p.β₂ ^ (t + 1))⁻¹ * v i j) + p.δ)

/-- Lines 8-13 of Algorithm 2 of arXiv 2511.04485 with gradient `g = g_{t+1}`.  The Q3R gradient
enters only in the last line, outside of the adaptive part. -/
def adamStep (p : AdamQ3RParams) (t : ℕ) (g : Matrix (Fin d₁) (Fin d₂) ℝ)
    (s : AdamQ3RState d₁ d₂) : AdamQ3RState d₁ d₂ :=
  let m := p.β₁ • s.m + (1 - p.β₁) • g
  let v := p.β₂ • s.v + (1 - p.β₂) • Matrix.of fun i j => g i j ^ 2
  { s with
    W := s.W - p.η • (adamDir p t m v + p.lam • reweight s.eps s.center s.W)
    m := m
    v := v }

/-- Algorithm 2 of arXiv 2511.04485, for a sequence `grad t` of minibatch gradient maps (line 7).
The paper starts with `ε = ∞`; here `ε₀` is any real number, and every `ε₀ ≥ σ_{r+1}(W₀)` gives the
same run. -/
def adamQ3R (p : AdamQ3RParams) (grad : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ → Matrix (Fin d₁) (Fin d₂) ℝ)
    (s₀ : AdamQ3RState d₁ d₂) : ℕ → AdamQ3RState d₁ d₂
  | 0 => s₀
  | t + 1 =>
    let s := reweightStep p t (adamQ3R p grad s₀ t)
    adamStep p t (grad t s.W) s

variable (p : AdamQ3RParams) (grad : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ → Matrix (Fin d₁) (Fin d₂) ℝ)
  (s₀ : AdamQ3RState d₁ d₂)

lemma adamQ3R_eps_of_mod (t : ℕ) (h : t % p.T = 0) :
    (adamQ3R p grad s₀ (t + 1)).eps =
      updateEps p.rT (adamQ3R p grad s₀ t).eps (adamQ3R p grad s₀ t).W := by
  simp [adamQ3R, adamStep, reweightStep, h]

lemma adamQ3R_eps_of_not_mod (t : ℕ) (h : t % p.T ≠ 0) :
    (adamQ3R p grad s₀ (t + 1)).eps = (adamQ3R p grad s₀ t).eps := by
  simp [adamQ3R, adamStep, reweightStep, h]

lemma adamQ3R_center_of_mod (t : ℕ) (h : t % p.T = 0) :
    (adamQ3R p grad s₀ (t + 1)).center = (adamQ3R p grad s₀ t).W := by
  simp [adamQ3R, adamStep, reweightStep, h]

lemma adamQ3R_center_of_not_mod (t : ℕ) (h : t % p.T ≠ 0) :
    (adamQ3R p grad s₀ (t + 1)).center = (adamQ3R p grad s₀ t).center := by
  simp [adamQ3R, adamStep, reweightStep, h]

/-- **Algorithm 2** of arXiv 2511.04485: the smoothing parameter is non-increasing along the run. -/
theorem adamQ3R_eps_antitone : Antitone fun t => (adamQ3R p grad s₀ t).eps := by
  refine antitone_nat_of_succ_le fun t => ?_
  by_cases h : t % p.T = 0
  · rw [adamQ3R_eps_of_mod p grad s₀ t h]
    exact updateEps_le _ _ _
  · rw [adamQ3R_eps_of_not_mod p grad s₀ t h]

/-- **Algorithm 2** of arXiv 2511.04485: between two reweighting steps the expansion point is the
iterate of the last reweighting step `k T`. -/
theorem adamQ3R_center (k : ℕ) {i : ℕ} (hi : i < p.T) :
    (adamQ3R p grad s₀ (k * p.T + i + 1)).center = (adamQ3R p grad s₀ (k * p.T)).W := by
  induction i with
  | zero => exact adamQ3R_center_of_mod p grad s₀ _ (by simp)
  | succ i ih =>
    have h1 : (k * p.T + (i + 1)) % p.T ≠ 0 := by
      rw [Nat.mul_add_mod_of_lt hi]
      omega
    have h2 := adamQ3R_center_of_not_mod p grad s₀ _ h1
    rw [h2]
    exact ih (by omega)

/-- **Algorithm 1 inside Algorithm 2** of arXiv 2511.04485: at a reweighting step with
`σ_{r+1}(W_t) ≤ ε_t`, the new rank envelope is at most the target rank. -/
theorem adamQ3R_rankEnv_le (t : ℕ) (h : t % p.T = 0)
    (hσ : sv (adamQ3R p grad s₀ t).W p.rT ≤ (adamQ3R p grad s₀ t).eps) :
    rankEnv (adamQ3R p grad s₀ (t + 1)).eps (adamQ3R p grad s₀ t).W ≤ p.rT := by
  rw [adamQ3R_eps_of_mod p grad s₀ t h]
  exact rankEnv_updateEps_le _ hσ

/-- **Line 13 of Algorithm 2** of arXiv 2511.04485, where `R_t` is the gradient of `Q3R` at `W_t`
by `hasGradientAt_Q3R`. -/
theorem adamQ3R_W_succ (t : ℕ) :
    (adamQ3R p grad s₀ (t + 1)).W = (adamQ3R p grad s₀ t).W -
      p.η • (adamDir p t (adamQ3R p grad s₀ (t + 1)).m (adamQ3R p grad s₀ (t + 1)).v +
        p.lam • reweight (reweightStep p t (adamQ3R p grad s₀ t)).eps
          (reweightStep p t (adamQ3R p grad s₀ t)).center (adamQ3R p grad s₀ t).W) := by
  by_cases h : t % p.T = 0 <;> simp [adamQ3R, adamStep, reweightStep, h]

/-- **Line 8 of Algorithm 2** of arXiv 2511.04485: the Q3R term does not enter the first moment. -/
theorem adamQ3R_m_succ (t : ℕ) :
    (adamQ3R p grad s₀ (t + 1)).m = p.β₁ • (adamQ3R p grad s₀ t).m +
      (1 - p.β₁) • grad t (adamQ3R p grad s₀ t).W := by
  by_cases h : t % p.T = 0 <;> simp [adamQ3R, adamStep, reweightStep, h]

/-- **Line 9 of Algorithm 2** of arXiv 2511.04485: the Q3R term does not enter the second moment. -/
theorem adamQ3R_v_succ (t : ℕ) :
    (adamQ3R p grad s₀ (t + 1)).v = p.β₂ • (adamQ3R p grad s₀ t).v +
      (1 - p.β₂) • Matrix.of fun i j => grad t (adamQ3R p grad s₀ t).W i j ^ 2 := by
  by_cases h : t % p.T = 0 <;> simp [adamQ3R, adamStep, reweightStep, h]

/-- One regularizer step decreases `Q3R` by `τ (1 - τ / 2) ‖R(W)‖²`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem Q3R_sub_smul_le (W' W : Matrix (Fin d₁) (Fin d₂) ℝ) (τ : ℝ) :
    Q3R ε W' (W - τ • reweight ε W' W) ≤
      Q3R ε W' W - τ * (1 - τ / 2) * ‖reweight ε W' W‖ ^ 2 := by
  set T := reweight ε W' W with hT
  have h1 := inner_reweight_self_le (ε := ε) (isSVD_svd W') T
  have h2 : ⟪W, reweight ε W' T⟫ = ‖T‖ ^ 2 := by
    rw [← reweight_symm, ← hT, real_inner_self_eq_norm_sq]
  have h4 : Q3R ε W' (W - τ • T) = Q3R ε W' W - τ * ‖T‖ ^ 2 +
      1 / 2 * τ ^ 2 * ⟪T, reweight ε W' T⟫ := by
    simp only [Q3R, map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, h2, RCLike.conj_to_real, ← hT, real_inner_self_eq_norm_sq]
    ring
  rw [h4]
  have h5 : 0 ≤ τ ^ 2 := sq_nonneg τ
  nlinarith

/-- **Majorization-minimization over one reweighting period** (not in arXiv 2511.04485, it follows
from the majorization of its footnote 2, here `FEps_le_quadModel`): the iteration
`W_{i+1} = W_i - τ R_{W₀,ε}(W_i)` with a frozen operator decreases `F_ε` for `τ ∈ (0, 2)`, and not
only the regularizer. -/
theorem FEps_period_le (hε : 0 < ε) (τ : ℝ) {w : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ}
    (hw : ∀ i, w (i + 1) = w i - τ • reweight ε (w 0) (w i)) (n : ℕ) :
    FEps ε (w n) ≤
      FEps ε (w 0) - τ * (1 - τ / 2) * ∑ i ∈ Finset.range n, ‖reweight ε (w 0) (w i)‖ ^ 2 := by
  have h1 : Q3R ε (w 0) (w n) ≤ Q3R ε (w 0) (w 0) -
      τ * (1 - τ / 2) * ∑ i ∈ Finset.range n, ‖reweight ε (w 0) (w i)‖ ^ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hw n, Finset.sum_range_succ, mul_add]
      have h2 := Q3R_sub_smul_le (ε := ε) (w 0) (w n) τ
      linarith
  have h2 := mm_descent hε (w 0) (w n)
  linarith

end Algorithms

/-! ### Generalized Hessians -/

section Hessian

variable {d₁ d₂ : ℕ} {ε : ℝ}

/-- **Section 4.1** of arXiv 2511.04485 (stated there without proof), at a point of twice
differentiability: if the Hessian `H` of `F_ε` exists at `W'`, then `H ⪯ R_{W',ε}`.  Proof: by the
majorization, `Q3R_{W',ε} - F_ε` has a minimum at `W'`. -/
theorem inner_hessian_le (hε : 0 < ε) {W' : Matrix (Fin d₁) (Fin d₂) ℝ}
    {H : Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ}
    (hH : HasFDerivAt (gradient (FEps ε)) H W') (T : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪T, H T⟫ ≤ ⟪T, reweight ε W' T⟫ := by
  by_contra hc
  rw [not_le] at hc
  let l : ℝ → Matrix (Fin d₁) (Fin d₂) ℝ := fun t => W' + t • T
  have hl : ∀ t, HasDerivAt l T t := fun t => by
    have h := ((hasDerivAt_id t).smul_const T).const_add W'
    simp only [one_smul] at h
    exact h
  have hl0 : l 0 = W' := by simp [l]
  let ψ : ℝ → ℝ := fun t => Q3R ε W' (l t) - FEps ε (l t)
  let d : ℝ → ℝ := fun t => ⟪reweight ε W' (l t) - gradient (FEps ε) (l t), T⟫
  have hψ : ∀ t, HasDerivAt ψ (d t) t := fun t => by
    have h1 := (hasGradientAt_Q3R ε W' (l t)).hasFDerivAt.comp_hasDerivAt t (hl t)
    have h2 := (hasGradientAt_FEps hε (l t)).hasFDerivAt.comp_hasDerivAt t (hl t)
    have h3 := h1.sub h2
    simp only [InnerProductSpace.toDual_apply_apply] at h3
    have h4 : d t = ⟪reweight ε W' (l t), T⟫ - ⟪reweight ε (l t) (l t), T⟫ := by
      simp only [d, inner_sub_left]
      rw [reweight_self_eq_gradient hε]
    rw [h4]
    exact h3
  have hd0 : d 0 = 0 := by
    simp only [d, hl0]
    rw [← reweight_self_eq_gradient hε, sub_self, inner_zero_left]
  have hdd : HasDerivAt d (⟪T, reweight ε W' T⟫ - ⟪T, H T⟫) 0 := by
    have h1 := (reweight ε W').hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hl 0)
    have h2 : HasFDerivAt (gradient (FEps ε)) H (l 0) := by rwa [hl0]
    have h3 := h2.comp_hasDerivAt (0 : ℝ) (hl 0)
    have h4 := (h1.sub h3).inner ℝ (hasDerivAt_const (0 : ℝ) T)
    refine h4.congr_deriv ?_
    rw [inner_zero_right, zero_add, inner_sub_left, real_inner_comm T (reweight ε W' T),
      real_inner_comm T (H T)]
  have hc' : ⟪T, reweight ε W' T⟫ - ⟪T, H T⟫ < 0 := by linarith
  have hs := hasDerivAt_iff_tendsto_slope.1 hdd
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope d 0 t < 0 :=
    (hs.eventually (gt_mem_nhds hc')).filter_mono (nhdsGT_le_nhdsNE 0)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hu0 : (0 : ℝ) < u := hu
  have hneg : ∀ t ∈ Set.Ioo 0 u, d t < 0 := fun t ht => by
    have h1 : slope d 0 t < 0 := hsub ht
    rw [slope_def_field, hd0, sub_zero, sub_zero] at h1
    by_contra h2
    have h3 := div_nonneg (not_lt.1 h2) ht.1.le
    linarith
  have hb : (0 : ℝ) < u / 2 := by positivity
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψ t).continuousAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope ψ d hb hψc.continuousOn fun x _ => hψ x
  have h1 := hneg ξ ⟨hξ.1, by linarith [hξ.2]⟩
  rw [hslope, sub_zero] at h1
  have h2 : ψ (u / 2) - ψ 0 < 0 := by
    by_contra h3
    have h4 := div_nonneg (not_lt.1 h3) hb.le
    linarith
  have h3 := mm_descent hε W' (l (u / 2))
  simp only [ψ, hl0] at h2
  linarith

/-- The limits of Hessians of `F_ε` at points converging to `W'`. -/
def hessianLimits (ε : ℝ) (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Set (Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ) :=
  {H | ∃ (x : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ)
      (H' : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ),
      Tendsto x atTop (𝓝 W') ∧ (∀ n, HasFDerivAt (gradient (FEps ε)) (H' n) (x n)) ∧
        ∀ T, Tendsto (fun n => H' n T) atTop (𝓝 (H T))}

/-- The generalized Hessian of Hiriart-Urruty, Strodiot and Nguyen (1984): the convex hull of the
limits of Hessians. -/
def genHessian (ε : ℝ) (W' : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Set (Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ) :=
  convexHull ℝ (hessianLimits ε W')

/-- **Section 4.1** of arXiv 2511.04485 (stated there without proof): every generalized Hessian of
`F_ε` at `W'` satisfies `∂²F_ε(W') ⪯ R_{W',ε}` in the Loewner order. -/
theorem inner_genHessian_le (hε : 0 < ε) {W' : Matrix (Fin d₁) (Fin d₂) ℝ}
    {H : Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ}
    (hH : H ∈ genHessian ε W') (T : Matrix (Fin d₁) (Fin d₂) ℝ) :
    ⟪T, H T⟫ ≤ ⟪T, reweight ε W' T⟫ := by
  have hsub : genHessian ε W' ⊆ {H | ⟪T, H T⟫ ≤ ⟪T, reweight ε W' T⟫} := by
    refine convexHull_min ?_ ?_
    · rintro H ⟨x, H', hx, hH', hlim⟩
      have h1 : Tendsto (fun n => ⟪T, H' n T⟫) atTop (𝓝 ⟪T, H T⟫) :=
        tendsto_const_nhds.inner (hlim T)
      have h2 : Tendsto (fun n => ⟪T, reweight ε (x n) T⟫) atTop (𝓝 ⟪T, reweight ε W' T⟫) :=
        tendsto_const_nhds.inner (((continuous_reweight hε T).tendsto W').comp hx)
      exact le_of_tendsto_of_tendsto' h1 h2 fun n => inner_hessian_le hε (hH' n) T
    · refine convex_halfSpace_le (f := fun H :
        Matrix (Fin d₁) (Fin d₂) ℝ →L[ℝ] Matrix (Fin d₁) (Fin d₂) ℝ => ⟪T, H T⟫) ⟨?_, ?_⟩ _
      · intro A B
        simp only [_root_.add_apply, inner_add_right]
      · intro c A
        simp only [_root_.smul_apply, inner_smul_right, smul_eq_mul]
  exact hsub hH

lemma sv_zero_le_norm (W : Matrix (Fin d₁) (Fin d₂) ℝ) : sv W 0 ≤ ‖W‖ := by
  rcases Nat.eq_zero_or_pos d₂ with h | h
  · rw [sv_eq_zero_of_right W (by omega)]
    exact norm_nonneg _
  · have h2 : sv W 0 ^ 2 ≤ ‖W‖ ^ 2 := by
      rw [sq_norm_eq_sum_sv]
      exact Finset.single_le_sum (f := fun j : Fin d₂ => sv W j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ (⟨0, h⟩ : Fin d₂))
    exact (pow_le_pow_iff_left₀ (sv_nonneg W 0) (norm_nonneg _) two_ne_zero).1 h2

lemma gradient_FEps_of_le (hε : 0 < ε) {W : Matrix (Fin d₁) (Fin d₂) ℝ} (hW : sv W 0 ≤ ε) :
    gradient (FEps ε) W = W := by
  have h := isSVD_svd W
  have e := h.eq
  rw [singularDiag_eq_dg] at e
  have h1 : (fun i => sv W i / max (sv W i / ε) 1 ^ 2) = sv W := by
    ext n
    have h2 : sv W n ≤ ε :=
      ((Matrix.toEuclideanLin W).singularValues_antitone (Nat.zero_le _)).trans hW
    have h3 : max (sv W n / ε) 1 = 1 := dEps_of_le hε h2
    rw [h3]
    simp
  rw [gradient_FEps hε h, h1]
  exact e.symm

/-- The generalized Hessian is not empty: near `0` we have `F_ε(W) = ½ ‖W‖²`, so that the identity
is a generalized Hessian at `0`.
Supporting result for arXiv 2511.04485, not stated in the paper. -/
theorem id_mem_genHessian (hε : 0 < ε) :
    ContinuousLinearMap.id ℝ (Matrix (Fin d₁) (Fin d₂) ℝ) ∈
      genHessian ε (0 : Matrix (Fin d₁) (Fin d₂) ℝ) := by
  have h1 : HasFDerivAt (gradient (FEps ε))
      (ContinuousLinearMap.id ℝ (Matrix (Fin d₁) (Fin d₂) ℝ))
      (0 : Matrix (Fin d₁) (Fin d₂) ℝ) := by
    refine (hasFDerivAt_id (0 : Matrix (Fin d₁) (Fin d₂) ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Matrix (Fin d₁) (Fin d₂) ℝ) hε] with W hW
    refine gradient_FEps_of_le hε ((sv_zero_le_norm W).trans ?_)
    simpa using (mem_ball_zero_iff.1 hW).le
  exact subset_convexHull ℝ _ ⟨fun _ => 0, fun _ => ContinuousLinearMap.id ℝ _,
    tendsto_const_nhds, fun _ => h1, fun _ => tendsto_const_nhds⟩

end Hessian

end

end LeanDLRA.Literature.P2511_04485

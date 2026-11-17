import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.LowRankDistance

/-!
# Low-rank gradient dynamics of a two-layer network with a smooth activation

Open problem OP-TR-39 of `docs/catalogue/survey/open-problems.json` (arXiv 2602.06208, Assumption
3.4, Sec. 3, App. C).  The model of the paper: inputs `X : d × N` (whitened,
`X Xᵀ = 1`), labels `Y : K × N`, a fixed second layer `W₂ : K × m`, a first layer `W₁ : m × d`
trained by gradient descent `W(t+1) = W(t) − η G₁(W(t))` on `½ ‖W₂ φ(W₁ X) − Y‖²_F` with an
elementwise activation `φ`, `φ(0) = 0`, `|φ''| ≤ μ`.  The gradient is
`G₁ = (W₂ᵀ Δ ⊙ φ'(W₁ X)) Xᵀ`, `Δ = W₂ φ(W₁ X) − Y` (`grad`).  The paper observes that `W₁`
trains in a `K × 2K` block of a fixed pair of bases and that `σ_{K+1}(G₁(t))` stays small, and
*assumes* these properties (Assumption 3.4, parts 2–3).

## What is proved (all unconditional, with explicit constants)

* **Exact decomposition** (`grad_eq`, `rank_linPart_le`): `G₁ = a W₂ᵀ Δ Xᵀ + E` with `a = φ'(0)`,
  `rank (a W₂ᵀ Δ Xᵀ) ≤ K` and `E = (W₂ᵀ Δ ⊙ (φ'(W₁ X) − a)) Xᵀ`.
* **Tail of the gradient** (`distLR_grad_le`, `norm_remE_le_of_whitened`):
  `dist_F(G₁, M_{≤ K}) ≤ ‖E‖_F ≤ μ ρ ‖W₂ᵀ Δ‖_F`, where `ρ = max |(W₁ X)ᵢⱼ|`.  By Eckart–Young
  the left side is `(∑_{i>K} σᵢ(G₁)²)^{1/2} ≥ σ_{K+1}(G₁)`.  At the paper's initialisation
  `W₁(0) = ε Q` this is `O(ε)`, the paper's `σᵢ(G₁(0)) = Θ(ε)`, `i > K` (upper half).
* **The invariant bases exist a priori** (`exists_bases`): for `K ≤ m` and `2K ≤ d` there are
  `U : m × K` with `U Uᵀ W₂ᵀ = W₂ᵀ` and `V : d × 2K` with `W₂ W(0) V Vᵀ = W₂ W(0)`,
  `Y Xᵀ V Vᵀ = Y Xᵀ`.  They depend on `W₂`, `W(0)`, `Y Xᵀ` only, not on `G₁(0)`.
* **Exact mechanism** (`one_sub_proj_grad`, `proj_grad_one_sub_proj`): the component of `G₁`
  normal to the range of `W₂ᵀ` is `(1 − U Uᵀ) E`, pure nonlinearity; and with
  `B = U Uᵀ (W₁ − W(0)) (1 − V Vᵀ)`, `U Uᵀ G₁ (1 − V Vᵀ) = a² W₂ᵀ W₂ B + a W₂ᵀ W₂ F Xᵀ (1 − V Vᵀ)
  + U Uᵀ E (1 − V Vᵀ)`, `F = φ(W₁ X) − a W₁ X`.
* **Linear activation** (`linear_normal_eq_zero`, `linear_eq_block`, `linear_rank_sub_le`): for
  `φ = a·id`, any `η`, `W(t) − W(0) = U Uᵀ (W(t) − W(0)) V Vᵀ` exactly, so `rank (W(t) − W(0)) ≤ K`
  for all `t`: the block structure of arXiv 2602.06208, Thm. 3.5, is exact for linear networks.
* **Smooth activation** (`norm_normal_left_le`, `norm_normal_right_le`,
  `normal_le_of_preactivation_bound`): with `η a² L² ≤ 2` (`L ≥ σ₁(W₂)` any Lipschitz constant
  of `W₂`, `W₂ᵀ`; `L = ‖W₂‖_F` works, `frobenius_lipschitz`) and `|(W(s) X)ᵢⱼ| ≤ ρ(s)`,
  `‖(1 − U Uᵀ)(W(t) − W(0))‖_F ≤ η μ ∑_{s<t} ρ(s) ‖W₂ᵀ Δ(s)‖_F` and
  `‖U Uᵀ (W(t) − W(0)) (1 − V Vᵀ)‖_F ≤ η μ ∑_{s<t} ρ(s) (‖W₂ᵀ Δ(s)‖_F + |a| L² ‖W(s) X‖_F / 2)`.
  The second block is driven through the non-expansive map `B ↦ (1 − η a² W₂ᵀ W₂) B`
  (`norm_sub_smul_gram_le`).  The paper's bound (Thm. 3.5) has the same `η`-sum structure but
  contains the assumed quantities `σ_{K+1}(G₁(t))` and the alignment `A(t)`; here both are
  replaced by the computable `μ ρ(s) ‖W₂ᵀ Δ(s)‖`.
* **Hypotheses are derivable and satisfiable** (`abs_deriv_sub_le_of_second_deriv`,
  `abs_sub_le_sq_of_deriv`, `sin_hypotheses`): `|φ''| ≤ μ` gives `|φ'(x) − φ'(0)| ≤ μ |x|`, which
  with `φ(0) = 0` gives `|φ(x) − φ'(0) x| ≤ μ x²/2`; `sin` satisfies both with `a = μ = 1`.
* **ReLU** (`relu_normal_component`): a `2 × 2` example where `G₁ = 2·1` and
  `(1 − U Uᵀ) G₁ = [[1, −1], [−1, 1]]` with all preactivations of modulus `1`: the normal
  component is a constant fraction of the gradient, so smoothness is what makes `G₁` close to
  rank `K`, not the architecture (part (ii) of the open problem at the level of one gradient).

## What stays open

The bounds are in terms of `ρ(s)` and `‖W₂ᵀ Δ(s)‖` along the trajectory.  An a priori bound on
`ρ(s)` (the network staying nearly linear) and the geometric decay of `‖G₁(t)‖_F` (Assumption
3.4, part 2) are not proved; numerically (scratch script) the normal components are indeed
bounded by the sums above at every step and vanish for the linear activation to round-off, but
for `tanh`, `sin` and softplus at scale `ρ ≈ 2–4` they are not small, so the near-linear regime
`μ ρ ≪ 1` is genuinely needed.  Joint training, `L = 4`, cross-entropy and adaptive optimisers
are not treated.
-/

open Finset
open scoped Matrix LeanDLRA.Frobenius RealInnerProductSpace

namespace LeanDLRA.Novel.OpTR39

variable {d N K m : Type*} [Fintype d] [Fintype N] [Fintype K] [Fintype m]

/-! ### Frobenius-norm lemmas -/

section Norms

variable {k l : Type*} [Fintype k] [Fintype l]

/-- An entrywise bound `|B i j| ≤ c |Z i j|` gives `‖B‖ ≤ c ‖Z‖`. -/
theorem norm_le_of_abs_le {B Z : Matrix k l ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |B i j| ≤ c * |Z i j|) : ‖B‖ ≤ c * ‖Z‖ := by
  have h2 : ‖B‖ ^ 2 ≤ (c * ‖Z‖) ^ 2 := by
    rw [mul_pow, Frobenius.norm_sq_eq_sum, Frobenius.norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
    rwa [sq_abs, mul_pow, sq_abs] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- The Hadamard product with an entrywise bounded matrix: `|B i j| ≤ c` gives
`‖A ⊙ B‖ ≤ c ‖A‖`. -/
theorem norm_hadamard_le {A B : Matrix k l ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, |B i j| ≤ c) :
    ‖A ⊙ B‖ ≤ c * ‖A‖ :=
  norm_le_of_abs_le hc fun i j => by
    rw [Matrix.hadamard_apply, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)

variable {r : ℕ}

/-- `‖Uᵀ M‖ ≤ ‖M‖` for `U` with orthonormal columns. -/
theorem norm_transpose_mul_le {U : Matrix k (Fin r) ℝ} (hU : Uᵀ * U = 1) (M : Matrix k l ℝ) :
    ‖Uᵀ * M‖ ≤ ‖M‖ := by
  have h : ‖Uᵀ * M‖ ^ 2 ≤ ‖M‖ * ‖Uᵀ * M‖ := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_left, Matrix.transpose_transpose]
    calc ⟪M, U * (Uᵀ * M)⟫ ≤ ‖M‖ * ‖U * (Uᵀ * M)‖ := real_inner_le_norm _ _
      _ = ‖M‖ * ‖Uᵀ * M‖ := by rw [Frobenius.norm_mul_of_orthonormal hU]
  rcases (norm_nonneg (Uᵀ * M)).lt_or_eq with h0 | h0
  · nlinarith
  · rw [← h0]; exact norm_nonneg _

/-- The orthogonal projection `U Uᵀ M` does not increase the Frobenius norm. -/
theorem norm_proj_le {U : Matrix k (Fin r) ℝ} (hU : Uᵀ * U = 1) (M : Matrix k l ℝ) :
    ‖U * Uᵀ * M‖ ≤ ‖M‖ := by
  rw [Matrix.mul_assoc, Frobenius.norm_mul_of_orthonormal hU]
  exact norm_transpose_mul_le hU M

/-- The complementary projection `(1 − U Uᵀ) M` does not increase the Frobenius norm. -/
theorem norm_one_sub_proj_le [DecidableEq k] {U : Matrix k (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (M : Matrix k l ℝ) : ‖(1 - U * Uᵀ) * M‖ ≤ ‖M‖ := by
  have h : ‖(1 - U * Uᵀ) * M‖ ^ 2 = ‖M‖ ^ 2 - ‖Uᵀ * M‖ ^ 2 := by
    rw [Matrix.sub_mul, Matrix.one_mul, norm_sub_sq_real, Matrix.mul_assoc,
      Frobenius.norm_mul_of_orthonormal hU, Frobenius.inner_mul_left',
      real_inner_self_eq_norm_sq]
    ring
  have h2 : ‖(1 - U * Uᵀ) * M‖ ^ 2 ≤ ‖M‖ ^ 2 := by rw [h]; nlinarith [norm_nonneg (Uᵀ * M)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- Right version: `‖M (1 − V Vᵀ)‖ ≤ ‖M‖`. -/
theorem norm_mul_one_sub_proj_le [DecidableEq l] {V : Matrix l (Fin r) ℝ} (hV : Vᵀ * V = 1)
    (M : Matrix k l ℝ) : ‖M * (1 - V * Vᵀ)‖ ≤ ‖M‖ := by
  rw [← Frobenius.norm_transpose, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact (norm_one_sub_proj_le hV Mᵀ).trans (Frobenius.norm_transpose M).le

/-- Whitened data: `X Xᵀ = 1` gives `‖M Xᵀ‖ ≤ ‖M‖` (right multiplication by `Xᵀ` is a partial
isometry). -/
theorem norm_mul_transpose_le_of_whitened [DecidableEq l] {X : Matrix l N ℝ} (hX : X * Xᵀ = 1)
    (M : Matrix k N ℝ) : ‖M * Xᵀ‖ ≤ ‖M‖ := by
  have hX' : Xᵀᵀ * Xᵀ = 1 := by rwa [Matrix.transpose_transpose]
  have h : ‖M * Xᵀ‖ ^ 2 ≤ ‖M‖ * ‖M * Xᵀ‖ := by
    rw [← real_inner_self_eq_norm_sq, Frobenius.inner_mul_right, Matrix.transpose_transpose]
    calc ⟪M, M * Xᵀ * X⟫ ≤ ‖M‖ * ‖M * Xᵀ * X‖ := real_inner_le_norm _ _
      _ = ‖M‖ * ‖M * Xᵀ‖ := by
        have := Frobenius.norm_mul_transpose_of_orthonormal hX' (M * Xᵀ)
        rw [Matrix.transpose_transpose] at this
        rw [this]
  rcases (norm_nonneg (M * Xᵀ)).lt_or_eq with h0 | h0
  · nlinarith
  · rw [← h0]; exact norm_nonneg _

end Norms

/-! ### The model -/

section Model

variable (X : Matrix d N ℝ) (Y : Matrix K N ℝ) (W₂ : Matrix K m ℝ) (φ dφ : ℝ → ℝ) (a : ℝ)

/-- The residual `Δ = W₂ φ(W₁ X) − Y` of the two-layer network with frozen second layer. -/
def residual (W₁ : Matrix m d ℝ) : Matrix K N ℝ := W₂ * (W₁ * X).map φ - Y

/-- The gradient of `½ ‖W₂ φ(W₁ X) − Y‖²_F` with respect to `W₁` by the chain rule,
`G₁ = (W₂ᵀ Δ ⊙ φ'(W₁ X)) Xᵀ` (arXiv 2602.06208, Sec. 3.1), with `dφ` the derivative of `φ`. -/
def grad (W₁ : Matrix m d ℝ) : Matrix m d ℝ :=
  ((W₂ᵀ * residual X Y W₂ φ W₁) ⊙ (W₁ * X).map dφ) * Xᵀ

/-- The gradient of the linearised network `W₂ (a W₁ X)` evaluated at the true residual:
`a W₂ᵀ Δ Xᵀ`, a matrix of rank at most `K`. -/
def linPart (W₁ : Matrix m d ℝ) : Matrix m d ℝ := W₂ᵀ * (a • (residual X Y W₂ φ W₁ * Xᵀ))

/-- The first-order nonlinearity remainder `E = (W₂ᵀ Δ ⊙ (φ'(W₁ X) − a)) Xᵀ = G₁ − a W₂ᵀ Δ Xᵀ`. -/
def remE (W₁ : Matrix m d ℝ) : Matrix m d ℝ :=
  ((W₂ᵀ * residual X Y W₂ φ W₁) ⊙ ((W₁ * X).map dφ - Matrix.of fun _ _ => a)) * Xᵀ

/-- The zeroth-order nonlinearity remainder `F = φ(W₁ X) − a W₁ X`. -/
def remF (W₁ : Matrix m d ℝ) : Matrix m N ℝ := (W₁ * X).map φ - a • (W₁ * X)

variable {X Y W₂ φ dφ a}

/-- The exact decomposition `G₁ = a W₂ᵀ Δ Xᵀ + E`. -/
theorem grad_eq (W₁ : Matrix m d ℝ) :
    grad X Y W₂ φ dφ W₁ = linPart X Y W₂ φ a W₁ + remE X Y W₂ φ dφ a W₁ := by
  have h : (W₂ᵀ * residual X Y W₂ φ W₁) ⊙ ((W₁ * X).map dφ - Matrix.of fun _ _ => a)
      = (W₂ᵀ * residual X Y W₂ φ W₁) ⊙ (W₁ * X).map dφ - a • (W₂ᵀ * residual X Y W₂ φ W₁) := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
    ring
  unfold grad linPart remE
  rw [h, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  abel

/-- The linear part has rank at most `K`: it factors through `W₂ᵀ : m × K`. -/
theorem rank_linPart_le (W₁ : Matrix m d ℝ) :
    (linPart X Y W₂ φ a W₁).rank ≤ Fintype.card K :=
  (Matrix.rank_mul_le_left _ _).trans (by simpa using (W₂ᵀ).rank_le_card_width)

omit [Fintype N] [Fintype m] in
/-- `φ(W₁ X) = a W₁ X + F`. -/
theorem map_eq_smul_add_remF (W₁ : Matrix m d ℝ) :
    (W₁ * X).map φ = a • (W₁ * X) + remF X φ a W₁ := by
  simp [remF]

/-- Entrywise bound on the first-order remainder: if `|φ'(x) − a| ≤ μ |x|` and the
preactivations satisfy `|(W₁ X)ᵢⱼ| ≤ ρ`, then `‖E‖_F ≤ μ ρ ‖W₂ᵀ Δ‖_F ‖Xᵀ‖_F`. -/
theorem norm_remE_le {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hdφ : ∀ x, |dφ x - a| ≤ μ * |x|)
    (W₁ : Matrix m d ℝ) (hW : ∀ i j, |(W₁ * X) i j| ≤ ρ) :
    ‖remE X Y W₂ φ dφ a W₁‖ ≤ μ * ρ * ‖W₂ᵀ * residual X Y W₂ φ W₁‖ * ‖Xᵀ‖ := by
  refine (Frobenius.norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine norm_hadamard_le (by positivity) fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply]
  exact (hdφ _).trans (mul_le_mul_of_nonneg_left (hW i j) hμ)

/-- Whitened version: `‖E‖_F ≤ μ ρ ‖W₂ᵀ Δ‖_F`. -/
theorem norm_remE_le_of_whitened [DecidableEq d] {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hdφ : ∀ x, |dφ x - a| ≤ μ * |x|) (hX : X * Xᵀ = 1)
    (W₁ : Matrix m d ℝ) (hW : ∀ i j, |(W₁ * X) i j| ≤ ρ) :
    ‖remE X Y W₂ φ dφ a W₁‖ ≤ μ * ρ * ‖W₂ᵀ * residual X Y W₂ φ W₁‖ := by
  refine (norm_mul_transpose_le_of_whitened hX _).trans ?_
  refine norm_hadamard_le (by positivity) fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply]
  exact (hdφ _).trans (mul_le_mul_of_nonneg_left (hW i j) hμ)

/-- Entrywise bound on the zeroth-order remainder: if `|φ(x) − a x| ≤ μ x² / 2` and
`|(W₁ X)ᵢⱼ| ≤ ρ`, then `‖F‖_F ≤ (μ ρ / 2) ‖W₁ X‖_F`. -/
theorem norm_remF_le {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ) (hφ : ∀ x, |φ x - a * x| ≤ μ / 2 * x ^ 2)
    (W₁ : Matrix m d ℝ) (hW : ∀ i j, |(W₁ * X) i j| ≤ ρ) :
    ‖remF X φ a W₁‖ ≤ μ * ρ / 2 * ‖W₁ * X‖ := by
  refine norm_le_of_abs_le (by positivity) fun i j => ?_
  simp only [remF, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  calc |φ ((W₁ * X) i j) - a * (W₁ * X) i j| ≤ μ / 2 * (W₁ * X) i j ^ 2 := hφ _
    _ = μ / 2 * |(W₁ * X) i j| * |(W₁ * X) i j| := by rw [mul_assoc, ← sq, sq_abs]
    _ ≤ μ / 2 * ρ * |(W₁ * X) i j| := by
        gcongr
        exact hW i j
    _ = μ * ρ / 2 * |(W₁ * X) i j| := by ring

/-- The Frobenius distance of the gradient to the matrices of rank at most `K` is bounded by the
first-order remainder: `dist(G₁, M_{≤ K}) ≤ ‖E‖_F`.  By Eckart–Young the left side is the tail
`(∑_{i>K} σᵢ(G₁)²)^{1/2}`, so in particular `σ_{K+1}(G₁) ≤ ‖E‖_F`. -/
theorem distLR_grad_le (W₁ : Matrix m d ℝ) :
    distLR (m := m) (n := d) (Fintype.card K) (grad X Y W₂ φ dφ W₁) ≤
      ‖remE X Y W₂ φ dφ a W₁‖ := by
  have h := distLR_le_norm_sub (X := grad X Y W₂ φ dφ W₁)
    (rank_linPart_le (X := X) (Y := Y) (W₂ := W₂) (φ := φ) (a := a) W₁)
  have e : grad X Y W₂ φ dφ W₁ - linPart X Y W₂ φ a W₁ = remE X Y W₂ φ dφ a W₁ := by
    rw [grad_eq (a := a) (dφ := dφ) W₁, add_sub_cancel_left]
  rwa [e] at h

end Model

/-! ### Gradient descent: the exact invariant block and its normal components -/

section Trajectory

variable {X : Matrix d N ℝ} {Y : Matrix K N ℝ} {W₂ : Matrix K m ℝ} {φ dφ : ℝ → ℝ} {a η : ℝ}
variable {r r' : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix d (Fin r') ℝ}

omit [Fintype K] in
/-- `W₂ = W₂ U Uᵀ` when `U Uᵀ` fixes the columns of `W₂ᵀ`. -/
theorem mul_proj_eq_of_capture (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) : W₂ * (U * Uᵀ) = W₂ := by
  have h := congrArg Matrix.transpose hUW
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose] at h

/-- The linear part lies in the range of `W₂ᵀ`: `(1 − U Uᵀ) (a W₂ᵀ Δ Xᵀ) = 0`. -/
theorem one_sub_proj_linPart [DecidableEq m] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (W₁ : Matrix m d ℝ) :
    (1 - U * Uᵀ) * linPart X Y W₂ φ a W₁ = 0 := by
  unfold linPart
  rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hUW, sub_self, Matrix.zero_mul]

/-- The component of the gradient normal to the range of `W₂ᵀ` is pure nonlinearity:
`(1 − U Uᵀ) G₁ = (1 − U Uᵀ) E`. -/
theorem one_sub_proj_grad [DecidableEq m] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (W₁ : Matrix m d ℝ) :
    (1 - U * Uᵀ) * grad X Y W₂ φ dφ W₁ = (1 - U * Uᵀ) * remE X Y W₂ φ dφ a W₁ := by
  rw [grad_eq (a := a), Matrix.mul_add, one_sub_proj_linPart hUW, zero_add]

/-- `U Uᵀ (a W₂ᵀ Δ Xᵀ) = W₂ᵀ (a Δ Xᵀ)`. -/
theorem proj_linPart (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (W₁ : Matrix m d ℝ) :
    U * Uᵀ * linPart X Y W₂ φ a W₁ = W₂ᵀ * (a • (residual X Y W₂ φ W₁ * Xᵀ)) := by
  unfold linPart
  rw [← Matrix.mul_assoc, hUW]

omit [Fintype K] in
/-- The residual times `Xᵀ` for whitened data: `Δ Xᵀ = a W₂ W₁ + W₂ F Xᵀ − Y Xᵀ`. -/
theorem residual_mul_transpose [DecidableEq d] (hX : X * Xᵀ = 1) (W₁ : Matrix m d ℝ) :
    residual X Y W₂ φ W₁ * Xᵀ =
      a • (W₂ * W₁) + W₂ * remF X φ a W₁ * Xᵀ - Y * Xᵀ := by
  rw [residual, map_eq_smul_add_remF (a := a) W₁, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc W₂ W₁ X,
    Matrix.mul_assoc (W₂ * W₁) X Xᵀ, hX, Matrix.mul_one]

/-- The block `U Uᵀ G₁ (1 − V Vᵀ)` of the gradient at `W₁`, for bases with `U Uᵀ W₂ᵀ = W₂ᵀ`,
`W₂ W₀ V Vᵀ = W₂ W₀`, `Y Xᵀ V Vᵀ = Y Xᵀ` and whitened data: writing
`B = U Uᵀ (W₁ − W₀) (1 − V Vᵀ)`, it equals
`a² W₂ᵀ W₂ B + a W₂ᵀ W₂ F Xᵀ (1 − V Vᵀ) + U Uᵀ E (1 − V Vᵀ)`.
For the linear activation (`E = F = 0`) this is the exact linear dynamics of the block. -/
theorem proj_grad_one_sub_proj [DecidableEq d] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (hX : X * Xᵀ = 1)
    {W₀ : Matrix m d ℝ} (hV1 : W₂ * W₀ * (V * Vᵀ) = W₂ * W₀) (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ)
    (W₁ : Matrix m d ℝ) :
    U * Uᵀ * grad X Y W₂ φ dφ W₁ * (1 - V * Vᵀ) =
      (a ^ 2) • (W₂ᵀ * (W₂ * (U * Uᵀ * (W₁ - W₀) * (1 - V * Vᵀ)))) +
        a • (W₂ᵀ * (W₂ * (remF X φ a W₁ * Xᵀ * (1 - V * Vᵀ)))) +
        U * Uᵀ * remE X Y W₂ φ dφ a W₁ * (1 - V * Vᵀ) := by
  have h1 : W₂ * W₁ * (1 - V * Vᵀ) = W₂ * (U * Uᵀ * (W₁ - W₀) * (1 - V * Vᵀ)) := by
    have e : W₂ * W₁ = W₂ * W₀ + W₂ * (U * Uᵀ * (W₁ - W₀)) := by
      rw [← Matrix.mul_assoc, mul_proj_eq_of_capture hUW, ← Matrix.mul_add, add_sub_cancel]
    rw [e, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_one, hV1, sub_self, zero_add,
      Matrix.mul_assoc]
  have h2 : Y * Xᵀ * (1 - V * Vᵀ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hV2, sub_self]
  have hR : residual X Y W₂ φ W₁ * Xᵀ * (1 - V * Vᵀ) =
      a • (W₂ * (U * Uᵀ * (W₁ - W₀) * (1 - V * Vᵀ))) +
        W₂ * (remF X φ a W₁ * Xᵀ * (1 - V * Vᵀ)) := by
    rw [residual_mul_transpose (a := a) hX, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, h1,
      h2, sub_zero, Matrix.mul_assoc W₂ (remF X φ a W₁) Xᵀ,
      Matrix.mul_assoc W₂ (remF X φ a W₁ * Xᵀ) (1 - V * Vᵀ)]
  have hlin : U * Uᵀ * linPart X Y W₂ φ a W₁ * (1 - V * Vᵀ) =
      (a ^ 2) • (W₂ᵀ * (W₂ * (U * Uᵀ * (W₁ - W₀) * (1 - V * Vᵀ)))) +
        a • (W₂ᵀ * (W₂ * (remF X φ a W₁ * Xᵀ * (1 - V * Vᵀ)))) := by
    rw [proj_linPart hUW, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hR, Matrix.mul_add,
      Matrix.mul_smul, smul_add, smul_smul, sq]
  rw [grad_eq (a := a), Matrix.mul_add, Matrix.add_mul, hlin]

/-- Non-expansiveness of one linearised step on the block: `‖B − c W₂ᵀ W₂ B‖ ≤ ‖B‖` when
`0 ≤ c` and `c L² ≤ 2`, where `L` is a Lipschitz constant of `M ↦ W₂ᵀ M` (e.g. `σ₁(W₂)`, or
`‖W₂‖_F`). -/
theorem norm_sub_smul_gram_le {c L : ℝ} (hc : 0 ≤ c) (hcL : c * L ^ 2 ≤ 2)
    (hL : ∀ M : Matrix K d ℝ, ‖W₂ᵀ * M‖ ≤ L * ‖M‖) (B : Matrix m d ℝ) :
    ‖B - c • (W₂ᵀ * (W₂ * B))‖ ≤ ‖B‖ := by
  have hin : ⟪B, W₂ᵀ * (W₂ * B)⟫ = ‖W₂ * B‖ ^ 2 := by
    rw [Frobenius.inner_mul_left', Matrix.transpose_transpose, real_inner_self_eq_norm_sq]
  have hG : ‖W₂ᵀ * (W₂ * B)‖ ^ 2 ≤ L ^ 2 * ‖W₂ * B‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
  have h2 : ‖B - c • (W₂ᵀ * (W₂ * B))‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hin]
    have hw : 0 ≤ ‖W₂ * B‖ ^ 2 := by positivity
    have hcc : c * ‖W₂ * B‖ ^ 2 * (c * L ^ 2 - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hc2 : c ^ 2 * ‖W₂ᵀ * (W₂ * B)‖ ^ 2 ≤ c ^ 2 * (L ^ 2 * ‖W₂ * B‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

variable {W : ℕ → Matrix m d ℝ}

/-- **Normal component in the range direction.**  Along gradient descent
`W(t+1) = W(t) − η G₁(W(t))`, the part of `W(t) − W(0)` orthogonal to the range of `W₂ᵀ` is
bounded by the accumulated first-order nonlinearity:
`‖(1 − U Uᵀ)(W(t) − W(0))‖_F ≤ η ∑_{s<t} ‖E(s)‖_F`.  For a linear activation it vanishes
identically.  No assumption on the trajectory is used. -/
theorem norm_normal_left_le [DecidableEq m] (hη : 0 ≤ η) (hU : Uᵀ * U = 1)
    (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    ‖(1 - U * Uᵀ) * (W t - W 0)‖ ≤ η * ∑ s ∈ range t, ‖remE X Y W₂ φ dφ a (W s)‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : W (t + 1) - W 0 = (W t - W 0) - η • grad X Y W₂ φ dφ (W t) := by
      rw [hW t]; abel
    rw [e, Matrix.mul_sub, Matrix.mul_smul, one_sub_proj_grad (a := a) hUW, sum_range_succ,
      mul_add]
    refine (norm_sub_le _ _).trans (add_le_add ih ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (norm_one_sub_proj_le hU _) hη

/-- **Normal component in the row direction.**  With `V` capturing the rows of `W₂ W(0)` and of
`Y Xᵀ`, whitened data, and a step size with `η a² L² ≤ 2` (`L ≥ 0` a common Lipschitz constant of
`M ↦ W₂ M` and `M ↦ W₂ᵀ M`, e.g. `σ₁(W₂)`), the block `U Uᵀ (W(t) − W(0)) (1 − V Vᵀ)` obeys
`‖·‖_F ≤ η ∑_{s<t} (‖E(s)‖_F + |a| L² ‖F(s)‖_F)`.  Mechanism: the linearised dynamics of this
block is the non-expansive map `B ↦ (1 − η a² W₂ᵀ W₂) B` (`proj_grad_one_sub_proj`,
`norm_sub_smul_gram_le`), driven only by the nonlinearity remainders. -/
theorem norm_normal_right_le [DecidableEq d] (hη : 0 ≤ η) (hU : Uᵀ * U = 1)
    (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (hV : Vᵀ * V = 1) (hV1 : W₂ * W 0 * (V * Vᵀ) = W₂ * W 0)
    (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ) (hX : X * Xᵀ = 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL1 : ∀ M : Matrix K d ℝ, ‖W₂ᵀ * M‖ ≤ L * ‖M‖)
    (hL2 : ∀ M : Matrix m d ℝ, ‖W₂ * M‖ ≤ L * ‖M‖) (hηL : η * a ^ 2 * L ^ 2 ≤ 2)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    ‖U * Uᵀ * (W t - W 0) * (1 - V * Vᵀ)‖ ≤
      η * ∑ s ∈ range t, (‖remE X Y W₂ φ dφ a (W s)‖ + |a| * L ^ 2 * ‖remF X φ a (W s)‖) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : W (t + 1) - W 0 = (W t - W 0) - η • grad X Y W₂ φ dφ (W t) := by
      rw [hW t]; abel
    set B := U * Uᵀ * (W t - W 0) * (1 - V * Vᵀ) with hB
    have e2 : U * Uᵀ * (W (t + 1) - W 0) * (1 - V * Vᵀ) =
        B - η • (U * Uᵀ * grad X Y W₂ φ dφ (W t) * (1 - V * Vᵀ)) := by
      rw [e, Matrix.mul_sub (U * Uᵀ), Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, proj_grad_one_sub_proj (a := a) hUW hX hV1 hV2, ← hB, sum_range_succ, mul_add]
    have hsplit : B - η • ((a ^ 2) • (W₂ᵀ * (W₂ * B)) +
        a • (W₂ᵀ * (W₂ * (remF X φ a (W t) * Xᵀ * (1 - V * Vᵀ)))) +
        U * Uᵀ * remE X Y W₂ φ dφ a (W t) * (1 - V * Vᵀ)) =
        (B - (η * a ^ 2) • (W₂ᵀ * (W₂ * B))) -
          η • (a • (W₂ᵀ * (W₂ * (remF X φ a (W t) * Xᵀ * (1 - V * Vᵀ)))) +
            U * Uᵀ * remE X Y W₂ φ dφ a (W t) * (1 - V * Vᵀ)) := by
      simp only [smul_add, smul_smul]; abel
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_sub_smul_gram_le (by positivity) hηL hL1 B).trans ih
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      refine mul_le_mul_of_nonneg_left ?_ hη
      refine (norm_add_le _ _).trans ?_
      rw [add_comm]
      refine add_le_add ?_ ?_
      · calc ‖U * Uᵀ * remE X Y W₂ φ dφ a (W t) * (1 - V * Vᵀ)‖
            ≤ ‖U * Uᵀ * remE X Y W₂ φ dφ a (W t)‖ := norm_mul_one_sub_proj_le hV _
          _ ≤ ‖remE X Y W₂ φ dφ a (W t)‖ := norm_proj_le hU _
      · rw [norm_smul, Real.norm_eq_abs, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
        calc ‖W₂ᵀ * (W₂ * (remF X φ a (W t) * Xᵀ * (1 - V * Vᵀ)))‖
            ≤ L * ‖W₂ * (remF X φ a (W t) * Xᵀ * (1 - V * Vᵀ))‖ := hL1 _
          _ ≤ L * (L * ‖remF X φ a (W t) * Xᵀ * (1 - V * Vᵀ)‖) :=
              mul_le_mul_of_nonneg_left (hL2 _) hL0
          _ ≤ L * (L * ‖remF X φ a (W t)‖) := by
              gcongr
              exact (norm_mul_one_sub_proj_le hV _).trans
                (norm_mul_transpose_le_of_whitened hX _)
          _ = L ^ 2 * ‖remF X φ a (W t)‖ := by ring

end Trajectory

/-! ### Existence of the bases, the linear case, and the assembled bound -/

section Bases

variable {X : Matrix d N ℝ} {Y : Matrix K N ℝ} {W₂ : Matrix K m ℝ}

/-- **The invariant bases exist a priori.**  If `K ≤ m` and `2K ≤ d` (the paper's `K < d/2`), there
are `U : m × K` with orthonormal columns capturing the range of `W₂ᵀ`, and `V : d × 2K` with
orthonormal columns capturing the rows of `W₂ W₀` and of `Y Xᵀ`.  Both depend only on `W₂`, `W₀`,
`Y Xᵀ`, not on the activation or on the trajectory. -/
theorem exists_bases (hK : Fintype.card K ≤ Fintype.card m)
    (hd : 2 * Fintype.card K ≤ Fintype.card d) (W₀ : Matrix m d ℝ) :
    ∃ (U : Matrix m (Fin (Fintype.card K)) ℝ) (V : Matrix d (Fin (2 * Fintype.card K)) ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ * W₂ᵀ = W₂ᵀ ∧ Vᵀ * V = 1 ∧
        W₂ * W₀ * (V * Vᵀ) = W₂ * W₀ ∧ Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ := by
  obtain ⟨U, hU, hUW⟩ :=
    exists_orthonormal_capture W₂ᵀ (by simpa using (W₂ᵀ).rank_le_card_width) hK
  have hrank : (Matrix.fromCols (W₂ * W₀)ᵀ (Y * Xᵀ)ᵀ).rank ≤ 2 * Fintype.card K := by
    have h := (Matrix.fromCols (W₂ * W₀)ᵀ (Y * Xᵀ)ᵀ).rank_le_card_width
    simp only [Fintype.card_sum] at h
    omega
  obtain ⟨V, hV, h1, h2⟩ := exists_orthonormal_capture_fromCols (W₂ * W₀)ᵀ (Y * Xᵀ)ᵀ hrank hd
  exact ⟨U, V, hU, hUW, hV, mul_proj_eq_of_capture h1, mul_proj_eq_of_capture h2⟩

end Bases

section Linear

variable {X : Matrix d N ℝ} {Y : Matrix K N ℝ} {W₂ : Matrix K m ℝ} {φ dφ : ℝ → ℝ} {a η : ℝ}
variable {r r' : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix d (Fin r') ℝ} {W : ℕ → Matrix m d ℝ}

omit [Fintype N] [Fintype K] [Fintype m] in
/-- For the linear activation `φ = a·id` the zeroth-order remainder vanishes. -/
theorem remF_eq_zero_of_linear (hφ : ∀ x, φ x = a * x) (W₁ : Matrix m d ℝ) :
    remF X φ a W₁ = 0 := by
  ext i j
  simp [remF, hφ]

/-- For the linear activation (`φ' ≡ a`) the first-order remainder vanishes. -/
theorem remE_eq_zero_of_linear (hdφ : ∀ x, dφ x = a) (W₁ : Matrix m d ℝ) :
    remE X Y W₂ φ dφ a W₁ = 0 := by
  unfold remE
  have h : (W₁ * X).map dφ - Matrix.of (fun _ _ => a) = 0 := by
    ext i j
    simp [hdφ]
  rw [h, Matrix.hadamard_zero, Matrix.zero_mul]

/-- **Exact invariance for the linear activation.**  Gradient descent on
`½ ‖W₂ (a W₁ X) − Y‖²` with whitened data, any step size `η`, keeps both normal components of
`W(t) − W(0)` exactly zero: `(1 − U Uᵀ)(W(t) − W(0)) = 0` and
`U Uᵀ (W(t) − W(0)) (1 − V Vᵀ) = 0` for all `t`. -/
theorem linear_normal_eq_zero [DecidableEq d] [DecidableEq m] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ)
    (hV1 : W₂ * W 0 * (V * Vᵀ) = W₂ * W 0) (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ)
    (hX : X * Xᵀ = 1) (hφ : ∀ x, φ x = a * x) (hdφ : ∀ x, dφ x = a)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    (1 - U * Uᵀ) * (W t - W 0) = 0 ∧ U * Uᵀ * (W t - W 0) * (1 - V * Vᵀ) = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : W (t + 1) - W 0 = (W t - W 0) - η • grad X Y W₂ φ dφ (W t) := by
      rw [hW t]; abel
    constructor
    · rw [e, Matrix.mul_sub, ih1, Matrix.mul_smul, one_sub_proj_grad (a := a) hUW,
        remE_eq_zero_of_linear hdφ, Matrix.mul_zero, smul_zero, sub_zero]
    · rw [e, Matrix.mul_sub (U * Uᵀ), Matrix.sub_mul, ih2, Matrix.mul_smul, Matrix.smul_mul,
        proj_grad_one_sub_proj (a := a) hUW hX hV1 hV2, ih2, remE_eq_zero_of_linear hdφ,
        remF_eq_zero_of_linear hφ, Matrix.mul_zero, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
      simp

/-- **The linear network trains in a fixed `K × 2K` block.**  Under the hypotheses of
`linear_normal_eq_zero`, `W(t) − W(0) = U Uᵀ (W(t) − W(0)) V Vᵀ`: the whole trajectory lies in
`W(0) + {U S Vᵀ}`, the block structure of arXiv 2602.06208, Thm. 3.5, exactly and for every `η`. -/
theorem linear_eq_block [DecidableEq d] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ)
    (hV1 : W₂ * W 0 * (V * Vᵀ) = W₂ * W 0) (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ)
    (hX : X * Xᵀ = 1) (hφ : ∀ x, φ x = a * x) (hdφ : ∀ x, dφ x = a)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    W t - W 0 = U * Uᵀ * (W t - W 0) * (V * Vᵀ) := by
  classical
  obtain ⟨h1, h2⟩ := linear_normal_eq_zero hUW hV1 hV2 hX hφ hdφ hW t
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
  exact h1.trans h2

/-- Consequently `rank (W(t) − W(0)) ≤ r` (`= K` for the bases of `exists_bases`). -/
theorem linear_rank_sub_le [DecidableEq d] (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ)
    (hV1 : W₂ * W 0 * (V * Vᵀ) = W₂ * W 0) (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ)
    (hX : X * Xᵀ = 1) (hφ : ∀ x, φ x = a * x) (hdφ : ∀ x, dφ x = a)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    (W t - W 0).rank ≤ r := by
  rw [linear_eq_block hUW hV1 hV2 hX hφ hdφ hW t]
  calc (U * Uᵀ * (W t - W 0) * (V * Vᵀ)).rank ≤ (U * Uᵀ * (W t - W 0)).rank :=
        Matrix.rank_mul_le_left _ _
    _ ≤ (U * Uᵀ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ U.rank := Matrix.rank_mul_le_left _ _
    _ ≤ r := by simpa using U.rank_le_card_width

end Linear

section Assembled

variable {X : Matrix d N ℝ} {Y : Matrix K N ℝ} {W₂ : Matrix K m ℝ} {φ dφ : ℝ → ℝ} {a η : ℝ}
variable {r r' : ℕ} {U : Matrix m (Fin r) ℝ} {V : Matrix d (Fin r') ℝ} {W : ℕ → Matrix m d ℝ}

/-- **Main bound.**  Smooth activation (`|φ'(x) − a| ≤ μ |x|`, `|φ(x) − a x| ≤ μ x²/2`, e.g.
`a = φ'(0)`, `μ = sup |φ''|`), whitened data, bases as in `exists_bases`, step size
`η a² L² ≤ 2`, and preactivation bounds `|(W(s) X)ᵢⱼ| ≤ ρ(s)` along the trajectory.  Then
for every `t`

* `‖(1 − U Uᵀ)(W(t) − W(0))‖_F ≤ η μ ∑_{s<t} ρ(s) ‖W₂ᵀ Δ(s)‖_F`,
* `‖U Uᵀ (W(t) − W(0)) (1 − V Vᵀ)‖_F ≤ η μ ∑_{s<t} ρ(s) (‖W₂ᵀ Δ(s)‖_F + |a| L² ‖W(s) X‖_F / 2)`,

and `dist(G₁(t), M_{≤ K}) ≤ μ ρ(t) ‖W₂ᵀ Δ(t)‖_F` (`distLR_grad_le`, `norm_remE_le_of_whitened`).
Everything is explicit and unconditional; the gradient-decay and tail-gap parts of
Assumption 3.4 of arXiv 2602.06208 are replaced by the computable quantities `ρ(s)`, `‖W₂ᵀ Δ(s)‖`.
The leakage out of the `K × 2K` block is `O(μ)` times the accumulated nonlinear scale of the
preactivations, which is the mechanism conjectured in the paper. -/
theorem normal_le_of_preactivation_bound [DecidableEq d] [DecidableEq m] {μ L : ℝ} {ρ : ℕ → ℝ}
    (hμ : 0 ≤ μ) (hρ : ∀ s, 0 ≤ ρ s) (hdφ : ∀ x, |dφ x - a| ≤ μ * |x|)
    (hφ : ∀ x, |φ x - a * x| ≤ μ / 2 * x ^ 2) (hpre : ∀ s i j, |(W s * X) i j| ≤ ρ s)
    (hη : 0 ≤ η) (hU : Uᵀ * U = 1) (hUW : U * Uᵀ * W₂ᵀ = W₂ᵀ) (hV : Vᵀ * V = 1)
    (hV1 : W₂ * W 0 * (V * Vᵀ) = W₂ * W 0) (hV2 : Y * Xᵀ * (V * Vᵀ) = Y * Xᵀ) (hX : X * Xᵀ = 1)
    (hL0 : 0 ≤ L) (hL1 : ∀ M : Matrix K d ℝ, ‖W₂ᵀ * M‖ ≤ L * ‖M‖)
    (hL2 : ∀ M : Matrix m d ℝ, ‖W₂ * M‖ ≤ L * ‖M‖) (hηL : η * a ^ 2 * L ^ 2 ≤ 2)
    (hW : ∀ t, W (t + 1) = W t - η • grad X Y W₂ φ dφ (W t)) (t : ℕ) :
    ‖(1 - U * Uᵀ) * (W t - W 0)‖ ≤
        η * μ * ∑ s ∈ range t, ρ s * ‖W₂ᵀ * residual X Y W₂ φ (W s)‖ ∧
      ‖U * Uᵀ * (W t - W 0) * (1 - V * Vᵀ)‖ ≤
        η * μ * ∑ s ∈ range t,
          ρ s * (‖W₂ᵀ * residual X Y W₂ φ (W s)‖ + |a| * L ^ 2 / 2 * ‖W s * X‖) := by
  have hE : ∀ s, ‖remE X Y W₂ φ dφ a (W s)‖ ≤ μ * (ρ s * ‖W₂ᵀ * residual X Y W₂ φ (W s)‖) :=
    fun s => by
      rw [← mul_assoc]
      exact norm_remE_le_of_whitened hμ (hρ s) hdφ hX (W s) (hpre s)
  have hF : ∀ s, ‖remF X φ a (W s)‖ ≤ μ * ρ s / 2 * ‖W s * X‖ :=
    fun s => norm_remF_le hμ (hρ s) hφ (W s) (hpre s)
  constructor
  · refine (norm_normal_left_le (a := a) hη hU hUW hW t).trans ?_
    rw [mul_assoc, Finset.mul_sum (range t) _ μ]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hE s) hη
  · refine (norm_normal_right_le hη hU hUW hV hV1 hV2 hX hL0 hL1 hL2 hηL hW t).trans ?_
    rw [mul_assoc, Finset.mul_sum (range t) _ μ]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => ?_) hη
    calc ‖remE X Y W₂ φ dφ a (W s)‖ + |a| * L ^ 2 * ‖remF X φ a (W s)‖
        ≤ μ * (ρ s * ‖W₂ᵀ * residual X Y W₂ φ (W s)‖) +
          |a| * L ^ 2 * (μ * ρ s / 2 * ‖W s * X‖) :=
          add_le_add (hE s) (mul_le_mul_of_nonneg_left (hF s) (by positivity))
      _ = μ * (ρ s * (‖W₂ᵀ * residual X Y W₂ φ (W s)‖ + |a| * L ^ 2 / 2 * ‖W s * X‖)) := by
          ring

/-- `L = ‖W₂‖_F` is an admissible Lipschitz constant in the theorems above (the sharp choice is
`σ₁(W₂)`). -/
theorem frobenius_lipschitz (W₂ : Matrix K m ℝ) :
    (∀ M : Matrix K d ℝ, ‖W₂ᵀ * M‖ ≤ ‖W₂‖ * ‖M‖) ∧ ∀ M : Matrix m d ℝ, ‖W₂ * M‖ ≤ ‖W₂‖ * ‖M‖ :=
  ⟨fun M => by rw [← Frobenius.norm_transpose W₂]; exact Frobenius.norm_mul_le _ _,
    fun M => Frobenius.norm_mul_le _ _⟩

end Assembled

/-! ### Activations: the remainder hypotheses from `φ(0) = 0`, `φ'(0) = a`, `|φ''| ≤ μ` -/

section Activation

/-- A function with nonnegative derivative on `[0, ∞)` is at least its value at `0` there. -/
private theorem le_of_deriv_nonneg_Ici {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (h : ∀ s, 0 ≤ s → 0 ≤ f' s) {x : ℝ} (hx : 0 ≤ x) : f 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hf s).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hs
      rw [(hf s).deriv]
      exact h s (le_of_lt hs)
  exact hmono (Set.mem_Ici.mpr le_rfl) hx hx

/-- A function with nonpositive derivative on `(−∞, 0]` is at least its value at `0` there. -/
private theorem le_of_deriv_nonpos_Iic {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (h : ∀ s, s ≤ 0 → f' s ≤ 0) {x : ℝ} (hx : x ≤ 0) : f 0 ≤ f x := by
  have hanti : AntitoneOn f (Set.Iic 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
      (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hf s).differentiableAt.differentiableWithinAt
    · rw [interior_Iic] at hs
      rw [(hf s).deriv]
      exact h s (le_of_lt hs)
  exact hanti hx (Set.mem_Iic.mpr le_rfl) hx

/-- **Second-order Taylor bound.**  If `φ(0) = 0`, `φ' = dφ` and `|dφ(x) − a| ≤ μ |x|`, then
`|φ(x) − a x| ≤ μ x² / 2`.  This derives the hypothesis `hφ` of
`normal_le_of_preactivation_bound` from `hdφ`. -/
theorem abs_sub_le_sq_of_deriv {φ dφ : ℝ → ℝ} {a μ : ℝ} (h0 : φ 0 = 0)
    (hd : ∀ x, HasDerivAt φ (dφ x) x) (hdφ : ∀ x, |dφ x - a| ≤ μ * |x|) (x : ℝ) :
    |φ x - a * x| ≤ μ / 2 * x ^ 2 := by
  have hp : ∀ s, HasDerivAt (fun s => μ / 2 * s ^ 2 - (φ s - a * s)) (μ * s - (dφ s - a)) s := by
    intro s
    have h1 : HasDerivAt (fun s => μ / 2 * s ^ 2 - (φ s - a * s))
        (μ / 2 * (↑(2 : ℕ) * s ^ (2 - 1)) - (dφ s - a * 1)) s :=
      ((hasDerivAt_pow 2 s).const_mul (μ / 2)).sub ((hd s).sub ((hasDerivAt_id s).const_mul a))
    exact h1.congr_deriv (by norm_num; ring)
  have hm : ∀ s, HasDerivAt (fun s => μ / 2 * s ^ 2 + (φ s - a * s)) (μ * s + (dφ s - a)) s := by
    intro s
    have h1 : HasDerivAt (fun s => μ / 2 * s ^ 2 + (φ s - a * s))
        (μ / 2 * (↑(2 : ℕ) * s ^ (2 - 1)) + (dφ s - a * 1)) s :=
      ((hasDerivAt_pow 2 s).const_mul (μ / 2)).add ((hd s).sub ((hasDerivAt_id s).const_mul a))
    exact h1.congr_deriv (by norm_num; ring)
  have hμ0 : 0 ≤ μ := by
    have := hdφ 1
    have := abs_nonneg (dφ 1 - a)
    simp only [abs_one, mul_one] at *
    linarith
  rw [abs_le]
  rcases le_total 0 x with hx | hx
  · have hpx := le_of_deriv_nonneg_Ici hp (fun s hs => by
      have := (abs_le.mp (hdφ s)).2
      rw [abs_of_nonneg hs] at this
      linarith) hx
    have hmx := le_of_deriv_nonneg_Ici hm (fun s hs => by
      have := (abs_le.mp (hdφ s)).1
      rw [abs_of_nonneg hs] at this
      linarith) hx
    simp only [h0, mul_zero, sub_self, zero_pow two_ne_zero, add_zero] at hpx hmx
    constructor <;> linarith
  · have hpx := le_of_deriv_nonpos_Iic hp (fun s hs => by
      have := (abs_le.mp (hdφ s)).1
      rw [abs_of_nonpos hs] at this
      linarith) hx
    have hmx := le_of_deriv_nonpos_Iic hm (fun s hs => by
      have := (abs_le.mp (hdφ s)).2
      rw [abs_of_nonpos hs] at this
      linarith) hx
    simp only [h0, mul_zero, sub_self, zero_pow two_ne_zero, add_zero] at hpx hmx
    constructor <;> linarith

/-- **First-order bound from a bounded second derivative.**  If `dφ' = ddφ` with `|ddφ| ≤ μ`, then
`|dφ(x) − dφ(0)| ≤ μ |x|`: the paper's assumption `|φ''| ≤ μ` gives `hdφ` with `a = φ'(0)`. -/
theorem abs_deriv_sub_le_of_second_deriv {dφ ddφ : ℝ → ℝ} {μ : ℝ}
    (hd : ∀ x, HasDerivAt dφ (ddφ x) x) (hμ : ∀ x, |ddφ x| ≤ μ) (x : ℝ) :
    |dφ x - dφ 0| ≤ μ * |x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := dφ) (f' := ddφ) (C := μ)
    (s := Set.univ) (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => by
      rw [Real.norm_eq_abs]; exact hμ s) convex_univ (Set.mem_univ 0) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- Instance: `φ = sin` satisfies the hypotheses with `a = 1`, `μ = 1`
(`|cos x − 1| ≤ |x|`, `|sin x − x| ≤ x²/2`); `tanh`, `GELU`, shifted softplus satisfy them with
their own `(a, μ)`. -/
theorem sin_hypotheses :
    (∀ x, |Real.cos x - 1| ≤ 1 * |x|) ∧ ∀ x : ℝ, |Real.sin x - 1 * x| ≤ 1 / 2 * x ^ 2 := by
  have hc : ∀ x, |Real.cos x - 1| ≤ 1 * |x| := fun x => by
    have := Real.abs_cos_sub_cos_le x 0
    simpa using this
  exact ⟨hc, abs_sub_le_sq_of_deriv Real.sin_zero Real.hasDerivAt_sin hc⟩

end Activation

/-! ### ReLU: the smoothness hypothesis cannot be dropped -/

section ReLU

/-- **ReLU counterexample to the mechanism.**  `d = N = m = 2`, `K = 1`, `X = 1`, `Y = (−1, −1)`,
`W₂ = (1, 1)`, `W₁ = [[1, −1], [−1, 1]]`, `φ = ReLU`.  The orthogonal projector onto the range
of `W₂ᵀ` is `P = ½ [[1, 1], [1, 1]] = U Uᵀ` with `U = (1, 1)ᵀ/√2`, and the gradient is
`G₁ = 2·1`, with normal component `(1 − P) G₁ = [[1, −1], [−1, 1]]`, of Frobenius norm
`‖G₁‖_F/√2`, although every preactivation has modulus `1` and the residual is bounded.  For ReLU
`φ'` is not Lipschitz near `0` (`μ = ∞`), and no bound of the form `μ ρ ‖W₂ᵀ Δ‖` can hold:
the rank-`K` structure of `G₁` is a consequence of the smoothness of `φ`, not of the
architecture. -/
theorem relu_normal_component :
    let X : Matrix (Fin 2) (Fin 2) ℝ := 1
    let Y : Matrix (Fin 1) (Fin 2) ℝ := !![-1, -1]
    let W₂ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]
    let W₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 1/2, 1/2]
    P * W₂ᵀ = W₂ᵀ ∧
      grad X Y W₂ (fun x => max x 0) (fun x => if 0 < x then 1 else 0) W₁ = !![2, 0; 0, 2] ∧
      (1 - P) * grad X Y W₂ (fun x => max x 0) (fun x => if 0 < x then 1 else 0) W₁ =
        !![1, -1; -1, 1] := by
  intro X Y W₂ W₁ P
  have hg : grad X Y W₂ (fun x => max x 0) (fun x => if 0 < x then 1 else 0) W₁ =
      !![2, 0; 0, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [grad, residual, X, Y, W₂, W₁, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.hadamard_apply, Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.vecHead,
        Matrix.vecTail] <;> norm_num
  refine ⟨?_, hg, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [P, W₂, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

end ReLU

end LeanDLRA.Novel.OpTR39

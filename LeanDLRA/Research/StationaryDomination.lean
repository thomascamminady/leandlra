import LeanDLRA.Research.StackedTruncation

/-!
# Domination of backward Euler runs by a stationary solution, and ranks free of the step count

Let `P ⪰ 0` and let `S` satisfy the stationary Lyapunov equation `P S + S P = F₀ + F` with
`F₀ ⪰ 0`. A backward Euler run `X_{j+1} + h (P X_{j+1} + X_{j+1} P) = X_j + h F` of the
differential Lyapunov equation `A' = -PA - AP + F` that starts below `S` stays below `S`
(`posSemidef_sub_of_lyapunov_run`): the difference `S - X_j` is a backward Euler run with the
forcing `F₀ ⪰ 0`, and the resolvent is positive (`LoewnerRank.posSemidef_of_add_smul_lyapunov`).
If `P ⪰ c > 0` and `F ⪰ 0`, the start condition `X₀ ⪯ S` follows from `P X₀ + X₀ P ⪯ F₀`
(`posSemidef_sub_of_lyapunov_le`), because the inverse of `M ↦ P M + M P` is positive
(`posSemidef_of_lyapunov`). Then the stationary equation has exactly one solution
(`existsUnique_lyapunov`), and for a start `X₀ = W₀ W₀ᵀ` and `t > 0` the right-hand side
`F₀ = t W₀ W₀ᵀ + t⁻¹ (P W₀)(P W₀)ᵀ` satisfies `P X₀ + X₀ P ⪯ F₀` and has rank at most twice the
number of columns of `W₀` (`posSemidef_sub_lyapunov_of_smul_add_inv_smul`). So a stationary
majorant `S` of the run whose right-hand side `F₀ + F` has low rank always exists
(`exists_lyapunov_posSemidef_sub`).

With the order argument for truncated runs (`LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run`)
and the monotonicity of the `ε`-rank in the Loewner order, the truncated iterates `Y_j`, which
are assumed positive semidefinite, satisfy from the first step on `Y_j ⪯ X_j ⪯ S` and

  `rank Y_j ≤ rank_θ(S)`

for every step size and every tolerance
(`rank_le_epsRank_of_truncated_lyapunov_run_of_stationary`): the bound does not depend on the
number of steps. The start is excluded: for `θ ≥ ‖S‖` the bound is `0`, while `Y_0` need not
vanish. The same holds for the rectangular scheme with stacked-factor truncation, with a
stationary solution `S` of the lifted problem
(`rank_le_epsRank_of_stacked_sylvester_run_of_stationary`).

For the Sylvester problem `A' = -PA - AQ + G Hᵀ` with `P ⪰ α`, `Q ⪰ β` and `a = α + β ≥ 0`
(neither `P` nor `Q` needs to be positive semidefinite), the shift `σ = (β - α) / 2` gives the
lifted operator `diag(P + σ, Q - σ)` with both blocks `⪰ a / 2`, and the shift is invisible in
the off-diagonal block (`StackedTruncation.shift_mul_add_mul_shift`). The end-to-end statement
`rank_le_epsRank_and_norm_sub_le_of_shifted_lift` collects: the off-diagonal block of the lifted
run is the backward Euler run of the Sylvester problem, the untruncated step of the scheme is
the backward Euler step of that problem from `L_j R_jᵀ`, `rank (L_{j+1} R_{j+1}ᵀ) ≤ rank_θ(S)`,
and `√2 ‖X_j - L_j R_jᵀ‖ ≤ E_j` whenever `E_{j+1} ≥ E_j / (1 + h a) + θ`.

A bound on `rank_θ(S)` itself, through the approximation of `1/x` by exponential sums (Dahmen,
DeVore, Grasedyck and Süli, arXiv 1407.6208, Lemma 5), is not part of this file.
-/

open scoped Matrix LeanDLRA.Frobenius
open Matrix

namespace LeanDLRA.StationaryDomination

/-! ### The stationary Lyapunov equation and domination -/

section Lyapunov

variable {n : Type*} [Fintype n]

/-- A Gram matrix `V Vᵀ` is positive semidefinite. -/
private theorem posSemidef_mul_transpose_self {p q : Type*} [Fintype q] (V : Matrix p q ℝ) :
    (V * Vᵀ).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose V

/-- The stationary equation `P M + M P = G` is a backward Euler step with step size `1 / (2c)`
for `P - c`. -/
private theorem add_inv_smul_lyapunov_sub [DecidableEq n] {P M G : Matrix n n ℝ} {c : ℝ}
    (hc : 0 < c) (hM : P * M + M * P = G) :
    M + (2 * c)⁻¹ • ((P - c • (1 : Matrix n n ℝ)) * M + M * (P - c • (1 : Matrix n n ℝ)))
      = (2 * c)⁻¹ • G := by
  have e : (2 * c)⁻¹ * c = 1 / 2 := by field_simp
  rw [← hM]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_sub, smul_smul, e]
  module

/-- **The inverse of the Lyapunov operator is positive.** If `P ⪰ c` with `c > 0` and
`P M + M P = G` with `G ⪰ 0`, then `M ⪰ 0`. (The equation is a backward Euler step with step
size `1 / (2c)` for `P - c`.) -/
theorem posSemidef_of_lyapunov [DecidableEq n] {P M G : Matrix n n ℝ} {c : ℝ}
    (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hc : 0 < c) (hG : G.PosSemidef)
    (hM : P * M + M * P = G) : M.PosSemidef := by
  have hk : 0 ≤ (2 * c)⁻¹ := by positivity
  exact LoewnerRank.posSemidef_of_add_smul_lyapunov hP (hG.smul hk) hk
    (add_inv_smul_lyapunov_sub hc hM)

/-- **The stationary Lyapunov equation has exactly one solution** if `P ⪰ c` with `c > 0`: the
operator `M ↦ P M + M P` is injective by the contraction of the backward Euler step, hence
bijective. It also follows from `LeanDLRA.compressedSylvester_existsUnique` (`V = 1`,
`A = B = -P`, `C = -G`), which this file does not import, to keep its imports minimal. -/
theorem existsUnique_lyapunov [DecidableEq n] {P : Matrix n n ℝ} {c : ℝ}
    (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hc : 0 < c) (G : Matrix n n ℝ) :
    ∃! S : Matrix n n ℝ, P * S + S * P = G := by
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ := LinearMap.mulLeft ℝ P + LinearMap.mulRight ℝ P
  have hL : ∀ M, L M = P * M + M * P := fun M => by simp [L]
  have hLi : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro M hM
    rw [hL] at hM
    have hP0 : (P - c • (1 : Matrix n n ℝ) - (0 : ℝ) • (1 : Matrix n n ℝ)).PosSemidef := by
      simpa using hP
    have h1 := LoewnerRank.mul_norm_le_of_add_smul_lyapunov hP0 (by positivity)
      (add_inv_smul_lyapunov_sub hc hM)
    simp only [smul_zero, norm_zero, mul_zero, add_zero, one_mul] at h1
    exact norm_le_zero_iff.mp h1
  obtain ⟨S, hS⟩ := LinearMap.injective_iff_surjective.mp hLi G
  refine ⟨S, (hL S).symm.trans hS, fun S' hS' => hLi ?_⟩
  rw [hS, hL, hS']

/-- **A low-rank right-hand side above the Lyapunov image of a start.** For symmetric `P`, a
factor `W` with columns indexed by `k` and `t > 0`, the matrix
`F₀ = t W Wᵀ + t⁻¹ (P W)(P W)ᵀ` satisfies `P (W Wᵀ) + (W Wᵀ) P ⪯ F₀` (the difference is
`t⁻¹ (t W - P W)(t W - P W)ᵀ`) and `rank F₀ ≤ 2 |k|`. -/
theorem posSemidef_sub_lyapunov_of_smul_add_inv_smul {k : Type*} [Fintype k] {P : Matrix n n ℝ}
    (hP : Pᵀ = P) (W : Matrix n k ℝ) {t : ℝ} (ht : 0 < t) :
    (t • (W * Wᵀ) + t⁻¹ • (P * W * (P * W)ᵀ) - (P * (W * Wᵀ) + W * Wᵀ * P)).PosSemidef ∧
      (t • (W * Wᵀ) + t⁻¹ • (P * W * (P * W)ᵀ)).rank ≤ 2 * Fintype.card k := by
  constructor
  · have e : t • (t • (W * Wᵀ) + t⁻¹ • (P * W * (P * W)ᵀ) - (P * (W * Wᵀ) + W * Wᵀ * P))
        = (t • W - P * W) * (t • W - P * W)ᵀ := by
      rw [transpose_sub, transpose_smul, transpose_mul, hP]
      simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      module
    have h := (posSemidef_mul_transpose_self (t • W - P * W)).smul (inv_nonneg.mpr ht.le)
    rwa [← e, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h
  · rw [show t • (W * Wᵀ) + t⁻¹ • (P * W * (P * W)ᵀ)
        = fromCols (t • W) (t⁻¹ • (P * W)) * (fromCols W (P * W))ᵀ by
      rw [transpose_fromCols, fromCols_mul_fromRows, Matrix.smul_mul, Matrix.smul_mul]]
    refine (Matrix.rank_mul_le_left _ _).trans ((fromCols _ _).rank_le_card_width.trans ?_)
    rw [Fintype.card_sum]
    omega

/-- **A start below the stationary solution.** If `P ⪰ c > 0`, `F ⪰ 0`, `P S + S P = F₀ + F`
and `P X₀ + X₀ P ⪯ F₀`, then `X₀ ⪯ S`. -/
theorem posSemidef_sub_of_lyapunov_le [DecidableEq n] {P F F₀ S X₀ : Matrix n n ℝ} {c : ℝ}
    (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hc : 0 < c) (hF : F.PosSemidef)
    (hS : P * S + S * P = F₀ + F) (hX₀ : (F₀ - (P * X₀ + X₀ * P)).PosSemidef) :
    (S - X₀).PosSemidef := by
  refine posSemidef_of_lyapunov hP hc (hX₀.add hF) ?_
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc P * S - P * X₀ + (S * P - X₀ * P) = (P * S + S * P) - (P * X₀ + X₀ * P) := by abel
    _ = F₀ - (P * X₀ + X₀ * P) + F := by rw [hS]; abel

/-- **A stationary majorant with a low-rank right-hand side.** If `P ⪰ c` with `c > 0`, then for
every factor `W₀` of a start `W₀ W₀ᵀ`, every factor `Wf` of the forcing `Wf Wfᵀ` and every
`t > 0`, the matrix `F₀ = t W₀ W₀ᵀ + t⁻¹ (P W₀)(P W₀)ᵀ` is positive semidefinite of rank at most
twice the number of columns of `W₀`, and the solution `S` of `P S + S P = F₀ + Wf Wfᵀ`
satisfies `W₀ W₀ᵀ ⪯ S`. -/
theorem exists_lyapunov_posSemidef_sub {k f : Type*} [Fintype k] [Fintype f] [DecidableEq n]
    {P : Matrix n n ℝ} {c t : ℝ} (hP : (P - c • (1 : Matrix n n ℝ)).PosSemidef) (hc : 0 < c)
    (ht : 0 < t) (W₀ : Matrix n k ℝ) (Wf : Matrix n f ℝ) :
    ∃ S : Matrix n n ℝ,
      P * S + S * P = t • (W₀ * W₀ᵀ) + t⁻¹ • (P * W₀ * (P * W₀)ᵀ) + Wf * Wfᵀ ∧
      (S - W₀ * W₀ᵀ).PosSemidef ∧
      (t • (W₀ * W₀ᵀ) + t⁻¹ • (P * W₀ * (P * W₀)ᵀ)).PosSemidef ∧
      (t • (W₀ * W₀ᵀ) + t⁻¹ • (P * W₀ * (P * W₀)ᵀ)).rank ≤ 2 * Fintype.card k := by
  have hPt : Pᵀ = P := by
    have h := hP.isHermitian.eq
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
      transpose_one] at h
    exact sub_left_injective h
  obtain ⟨S, hS, -⟩ := existsUnique_lyapunov hP hc
    (t • (W₀ * W₀ᵀ) + t⁻¹ • (P * W₀ * (P * W₀)ᵀ) + Wf * Wfᵀ)
  obtain ⟨h1, h2⟩ := posSemidef_sub_lyapunov_of_smul_add_inv_smul hPt W₀ ht
  exact ⟨S, hS, posSemidef_sub_of_lyapunov_le hP hc (posSemidef_mul_transpose_self Wf) hS h1,
    ((posSemidef_mul_transpose_self W₀).smul ht.le).add
      ((posSemidef_mul_transpose_self _).smul (inv_nonneg.mpr ht.le)), h2⟩

/-- **Domination by a stationary solution.** Let `P ⪰ 0`, `h ≥ 0`, and let `S` satisfy
`P S + S P = F₀ + F` with `F₀ ⪰ 0`. Every backward Euler run
`X_{j+1} + h (P X_{j+1} + X_{j+1} P) = X_j + h F` that starts below `S` stays below `S`:
`X_j ⪯ S` for all `j ≤ N`. No sign condition on `F` is needed. -/
theorem posSemidef_sub_of_lyapunov_run {P F F₀ S : Matrix n n ℝ} {h : ℝ} (hP : P.PosSemidef)
    (hF₀ : F₀.PosSemidef) (hh : 0 ≤ h) (hS : P * S + S * P = F₀ + F) {N : ℕ}
    {X : ℕ → Matrix n n ℝ}
    (hX : ∀ j < N, X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P) = X j + h • F)
    (hX0 : (S - X 0).PosSemidef) : ∀ j ≤ N, (S - X j).PosSemidef := by
  intro j
  induction j with
  | zero => intro _; exact hX0
  | succ j ih =>
    intro hj
    have hlt : j < N := hj
    refine LoewnerRank.posSemidef_of_add_smul_lyapunov hP ((ih hlt.le).add (hF₀.smul hh)) hh ?_
    have e : S - X (j + 1) + h • (P * (S - X (j + 1)) + (S - X (j + 1)) * P)
        = S + h • (P * S + S * P) - (X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      module
    rw [e, hS, hX j hlt]
    module

/-- **Ranks of a truncated backward Euler run, bounded independently of the step count.** In the
setting of `LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run` (the truncated iterates
`Y_{j+1}` are assumed positive semidefinite), let `S` satisfy `P S + S P = F₀ + F` with `F₀ ⪰ 0`
and `X₀ ⪯ S`. Then after every step `Y_{j+1} ⪯ X_{j+1} ⪯ S` and `rank Y_{j+1} ≤ rank_θ(S)`, for
every step size and every tolerance. -/
theorem rank_le_epsRank_of_truncated_lyapunov_run_of_stationary {P F F₀ S : Matrix n n ℝ}
    {h θ : ℝ} (hP : P.PosSemidef) (hF : F.PosSemidef) (hF₀ : F₀.PosSemidef) (hh : 0 ≤ h)
    (hθ : 0 ≤ θ) (hS : P * S + S * P = F₀ + F) {N : ℕ} {X Y Yh : ℕ → Matrix n n ℝ}
    (hX : ∀ j < N, X (j + 1) + h • (P * X (j + 1) + X (j + 1) * P) = X j + h • F)
    (hYh : ∀ j < N, Yh (j + 1) + h • (P * Yh (j + 1) + Yh (j + 1) * P) = Y j + h • F)
    (hY0 : (Y 0).PosSemidef) (hXY0 : (X 0 - Y 0).PosSemidef) (hSX0 : (S - X 0).PosSemidef)
    (hYpos : ∀ j < N, (Y (j + 1)).PosSemidef)
    (hYle : ∀ j < N, (Yh (j + 1) - Y (j + 1)).PosSemidef)
    (hYrank : ∀ j < N, (Y (j + 1)).rank ≤ epsRank θ (Yh (j + 1))) :
    ∀ j < N, (X (j + 1) - Y (j + 1)).PosSemidef ∧ (S - X (j + 1)).PosSemidef ∧
      (Y (j + 1)).rank ≤ epsRank θ S := by
  have hrun := LoewnerRank.rank_le_epsRank_of_truncated_lyapunov_run hP hF hh hθ hX hYh hY0
    hXY0 hYpos hYle hYrank
  have hdom := posSemidef_sub_of_lyapunov_run hP hF₀ hh hS hX hSX0
  intro j hj
  obtain ⟨-, -, hXY, hr⟩ := hrun j hj
  have hXp : (X (j + 1)).PosSemidef := by simpa using hXY.add (hYpos j hj)
  exact ⟨hXY, hdom (j + 1) hj,
    hr.trans (LoewnerRank.epsRank_le_epsRank_of_posSemidef hXp (hdom (j + 1) hj) hθ)⟩

end Lyapunov

/-! ### The stacked-factor scheme for a Sylvester equation -/

section Stacked

variable {m n k f : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype f] [DecidableEq k]
  {P : Matrix m m ℝ} {Q : Matrix n n ℝ} {Wf : Matrix (m ⊕ n) f ℝ} {h θ : ℝ} {N : ℕ}
  {X : ℕ → Matrix (m ⊕ n) (m ⊕ n) ℝ} {W Wh : ℕ → Matrix (m ⊕ n) k ℝ} {Z : ℕ → Matrix k k ℝ}
  {S F₀ : Matrix (m ⊕ n) (m ⊕ n) ℝ}

/-- **Ranks of the stacked-factor scheme, bounded independently of the step count.** In the
setting of `StackedTruncation.rank_le_epsRank_of_stacked_sylvester_run`, let `S` satisfy
`𝒫 S + S 𝒫 = F₀ + Wf Wfᵀ` for the lifted operator `𝒫 = diag(P, Q)`, with `F₀ ⪰ 0` and
`X₀ ⪯ S`. Then after every step `W_{j+1} W_{j+1}ᵀ ⪯ X_{j+1} ⪯ S` and the computed iterates
satisfy `rank (L_{j+1} R_{j+1}ᵀ) ≤ rank_θ(S)`, for every step size and every tolerance. -/
theorem rank_le_epsRank_of_stacked_sylvester_run_of_stationary (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (hh : 0 ≤ h) (hθ : 0 ≤ θ)
    (hX : ∀ j < N, X (j + 1) + h • (fromBlocks P 0 0 Q * X (j + 1)
      + X (j + 1) * fromBlocks P 0 0 Q) = X j + h • (Wf * Wfᵀ))
    (hWh : ∀ j < N, Wh (j + 1) * (Wh (j + 1))ᵀ + h • (fromBlocks P 0 0 Q
      * (Wh (j + 1) * (Wh (j + 1))ᵀ) + Wh (j + 1) * (Wh (j + 1))ᵀ * fromBlocks P 0 0 Q)
      = W j * (W j)ᵀ + h • (Wf * Wfᵀ))
    (hX0 : (X 0 - W 0 * (W 0)ᵀ).PosSemidef)
    (hW : ∀ j < N, W (j + 1) = Wh (j + 1) * Z j)
    (hZ : ∀ j < N, (1 - Z j * (Z j)ᵀ).PosSemidef)
    (hZrank : ∀ j < N, (Z j).rank ≤ epsRank θ (Wh (j + 1) * (Wh (j + 1))ᵀ))
    (hF₀ : F₀.PosSemidef)
    (hS : fromBlocks P 0 0 Q * S + S * fromBlocks P 0 0 Q = F₀ + Wf * Wfᵀ)
    (hSX0 : (S - X 0).PosSemidef) :
    ∀ j < N, (X (j + 1) - W (j + 1) * (W (j + 1))ᵀ).PosSemidef ∧ (S - X (j + 1)).PosSemidef ∧
      ((W (j + 1)).toRows₁ * (W (j + 1)).toRows₂ᵀ).rank ≤ epsRank θ S := by
  have hrun := StackedTruncation.rank_le_epsRank_of_stacked_sylvester_run hP hQ hh hθ hX hWh
    hX0 hW hZ hZrank
  have hdom := posSemidef_sub_of_lyapunov_run (StackedTruncation.posSemidef_fromBlocks_diag hP hQ)
    hF₀ hh hS hX hSX0
  intro j hj
  obtain ⟨-, hr, hle⟩ := hrun j hj
  have hWp := posSemidef_mul_transpose_self (W (j + 1))
  have hXp : (X (j + 1)).PosSemidef := by simpa using hle.add hWp
  exact ⟨hle, hdom (j + 1) hj,
    hr.trans (LoewnerRank.epsRank_le_epsRank_of_posSemidef hXp (hdom (j + 1) hj) hθ)⟩

/-- **Ranks and errors of the stacked-factor scheme for a Sylvester equation through the shifted
lift.** Let `P ⪰ α` and `Q ⪰ β` with `a = α + β ≥ 0` (neither `P` nor `Q` needs to be positive
semidefinite), let `2σ = β - α`, and lift with the operator `𝒫 = diag(P + σ, Q - σ)` (both blocks
`⪰ a / 2`) and the stacked forcing factor `Wf = [G; H]`. Let `X` be the backward Euler run of the
lifted Lyapunov problem, let the scheme store stacked factors `W_j = [L_j; R_j]` truncated as in
`StackedTruncation.rank_le_epsRank_of_stacked_sylvester_run`, and let `S` satisfy
`𝒫 S + S 𝒫 = F₀ + Wf Wfᵀ` with `F₀ ⪰ 0` and `X₀ ⪯ S`. Then for every step
* the off-diagonal block of `X` is the backward Euler run of `A' = -PA - AQ + G Hᵀ` with the
  unshifted `P` and `Q`;
* before truncation the scheme takes the backward Euler step of the same problem from `L_j R_jᵀ`;
* `rank (L_{j+1} R_{j+1}ᵀ) ≤ rank_θ(S)`, for every step size and every tolerance;
* `√2 ‖X_j - L_j R_jᵀ‖ ≤ E_j` for the off-diagonal block `X_j` of the lifted run and every
  sequence with `E₀ ≥ ‖X₀ - W₀ W₀ᵀ‖` and `E_{j+1} ≥ E_j / (1 + h a) + θ`. -/
theorem rank_le_epsRank_and_norm_sub_le_of_shifted_lift [DecidableEq m] [DecidableEq n]
    {α β σ : ℝ} {PQ : Matrix (m ⊕ n) (m ⊕ n) ℝ} {E : ℕ → ℝ}
    (hP : (P - α • (1 : Matrix m m ℝ)).PosSemidef) (hQ : (Q - β • (1 : Matrix n n ℝ)).PosSemidef)
    (ha : 0 ≤ α + β) (hσ : 2 * σ = β - α)
    (hPQ : PQ = fromBlocks (P + σ • (1 : Matrix m m ℝ)) 0 0 (Q - σ • (1 : Matrix n n ℝ)))
    (hh : 0 ≤ h) (hθ : 0 ≤ θ)
    (hX : ∀ j < N, X (j + 1) + h • (PQ * X (j + 1) + X (j + 1) * PQ) = X j + h • (Wf * Wfᵀ))
    (hWh : ∀ j < N, Wh (j + 1) * (Wh (j + 1))ᵀ + h • (PQ * (Wh (j + 1) * (Wh (j + 1))ᵀ)
      + Wh (j + 1) * (Wh (j + 1))ᵀ * PQ) = W j * (W j)ᵀ + h • (Wf * Wfᵀ))
    (hX0 : (X 0 - W 0 * (W 0)ᵀ).PosSemidef)
    (hW : ∀ j < N, W (j + 1) = Wh (j + 1) * Z j)
    (hZ : ∀ j < N, (1 - Z j * (Z j)ᵀ).PosSemidef)
    (hZrank : ∀ j < N, (Z j).rank ≤ epsRank θ (Wh (j + 1) * (Wh (j + 1))ᵀ))
    (hT : ∀ j < N, ‖Wh (j + 1) * (Wh (j + 1))ᵀ - W (j + 1) * (W (j + 1))ᵀ‖ ≤ θ)
    (hF₀ : F₀.PosSemidef) (hS : PQ * S + S * PQ = F₀ + Wf * Wfᵀ) (hSX0 : (S - X 0).PosSemidef)
    (hE0 : ‖X 0 - W 0 * (W 0)ᵀ‖ ≤ E 0)
    (hE : ∀ j < N, E j / (1 + h * (α + β)) + θ ≤ E (j + 1)) :
    (∀ j < N, (X (j + 1)).toBlocks₁₂ + h • (P * (X (j + 1)).toBlocks₁₂
        + (X (j + 1)).toBlocks₁₂ * Q) = (X j).toBlocks₁₂ + h • (Wf.toRows₁ * Wf.toRows₂ᵀ) ∧
      (Wh (j + 1)).toRows₁ * (Wh (j + 1)).toRows₂ᵀ
        + h • (P * ((Wh (j + 1)).toRows₁ * (Wh (j + 1)).toRows₂ᵀ)
          + (Wh (j + 1)).toRows₁ * (Wh (j + 1)).toRows₂ᵀ * Q)
        = (W j).toRows₁ * (W j).toRows₂ᵀ + h • (Wf.toRows₁ * Wf.toRows₂ᵀ) ∧
      ((W (j + 1)).toRows₁ * (W (j + 1)).toRows₂ᵀ).rank ≤ epsRank θ S) ∧
    ∀ j ≤ N, Real.sqrt 2 * ‖(X j).toBlocks₁₂ - (W j).toRows₁ * (W j).toRows₂ᵀ‖ ≤ E j := by
  subst hPQ
  have hσ' : σ = (β - α) / 2 := by linarith
  subst hσ'
  have hc : 0 ≤ (α + β) / 2 := by linarith
  have hPc : (P + ((β - α) / 2) • (1 : Matrix m m ℝ)
      - ((α + β) / 2) • (1 : Matrix m m ℝ)).PosSemidef := by
    convert hP using 1
    module
  have hQc : (Q - ((β - α) / 2) • (1 : Matrix n n ℝ)
      - ((α + β) / 2) • (1 : Matrix n n ℝ)).PosSemidef := by
    convert hQ using 1
    module
  have hP0 : (P + ((β - α) / 2) • (1 : Matrix m m ℝ)).PosSemidef := by
    simpa using hPc.add (Matrix.PosSemidef.one.smul hc)
  have hQ0 : (Q - ((β - α) / 2) • (1 : Matrix n n ℝ)).PosSemidef := by
    simpa using hQc.add (Matrix.PosSemidef.one.smul hc)
  have hE' : ∀ j < N, E j / (1 + 2 * h * ((α + β) / 2)) + θ ≤ E (j + 1) := fun j hj => by
    rw [show 2 * h * ((α + β) / 2) = h * (α + β) by ring]
    exact hE j hj
  have hrun := StackedTruncation.rank_le_epsRank_of_stacked_sylvester_run hP0 hQ0 hh hθ hX hWh
    hX0 hW hZ hZrank
  have hrank := rank_le_epsRank_of_stacked_sylvester_run_of_stationary hP0 hQ0 hh hθ hX hWh
    hX0 hW hZ hZrank hF₀ hS hSX0
  refine ⟨fun j hj => ⟨?_, ?_, (hrank j hj).2.2⟩,
    StackedTruncation.norm_sub_le_of_stacked_sylvester_run hPc hQc hh hc hθ hX hWh hX0 hW hZ
      hZrank hT hE0 hE'⟩
  · have h1 := (hrun j hj).1
    rwa [StackedTruncation.shift_mul_add_mul_shift] at h1
  · have h1 := StackedTruncation.toBlocks₁₂_add_smul_lyapunov (hWh j hj)
    rw [StackedTruncation.shift_mul_add_mul_shift, StackedTruncation.toBlocks₁₂_mul_transpose]
      at h1
    rw [h1, ← StackedTruncation.toBlocks₁₂_mul_transpose,
      ← StackedTruncation.toBlocks₁₂_mul_transpose]
    rfl

end Stacked

end LeanDLRA.StationaryDomination

/-! ### Non-vacuity -/

namespace LeanDLRA.StationaryDominationExample

noncomputable section

/-- The stacked vector `[1; 1]`. -/
def exA : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ := fromRows 1 1

/-- The stacked vector `[1; -1]`. -/
def exB : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ := fromRows 1 (-1)

/-- The stacked factor `W₀ = [3 exA, 0]` of the start. -/
def exW₀ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := fromCols ((3 : ℝ) • exA) 0

/-- The stacked factor `Ŵ₁ = [exA, exB / 2]` of the first step. -/
def exWh : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := fromCols exA ((1 / 2 : ℝ) • exB)

/-- The truncated stacked factor `W₁ = [exA, 0]`. -/
def exW₁ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := fromCols exA 0

/-- The stacked factor `[G; H] = (3/4) exB` of the forcing. -/
def exWf : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ := (3 / 4 : ℝ) • exB

/-- The truncation `Z = diag(1, 0)`, the projector onto the first column. -/
def exZ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := fromBlocks 1 0 0 0

theorem exA_mul_transpose : exA * exAᵀ = fromBlocks 1 1 1 1 := by
  rw [exA, transpose_fromRows, fromRows_mul_fromCols]
  simp

theorem exB_mul_transpose : exB * exBᵀ = fromBlocks 1 (-1) (-1) 1 := by
  rw [exB, transpose_fromRows, fromRows_mul_fromCols]
  simp

theorem exWh_mul_transpose : exWh * exWhᵀ = exA * exAᵀ + (1 / 4 : ℝ) • (exB * exBᵀ) := by
  rw [exWh, transpose_fromCols, fromCols_mul_fromRows, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  norm_num

theorem exW₀_mul_transpose : exW₀ * exW₀ᵀ = (9 : ℝ) • (exA * exAᵀ) := by
  rw [exW₀, transpose_fromCols, fromCols_mul_fromRows, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, transpose_zero, Matrix.mul_zero, add_zero]
  norm_num

theorem exW₁_mul_transpose : exW₁ * exW₁ᵀ = exA * exAᵀ := by
  rw [exW₁, transpose_fromCols, fromCols_mul_fromRows, transpose_zero, Matrix.mul_zero, add_zero]

theorem exWf_mul_transpose : exWf * exWfᵀ = (9 / 16 : ℝ) • (exB * exBᵀ) := by
  rw [exWf, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

/-- One backward Euler step with `h = 4` for the lifted operator `1` and the forcing
`exWf exWfᵀ`, from `exW₀ exW₀ᵀ`, lands on `exWh exWhᵀ`. -/
theorem exWh_step : exWh * exWhᵀ + (4 : ℝ) • (1 * (exWh * exWhᵀ) + exWh * exWhᵀ * 1)
    = exW₀ * exW₀ᵀ + (4 : ℝ) • (exWf * exWfᵀ) := by
  rw [Matrix.one_mul, Matrix.mul_one, exWh_mul_transpose, exW₀_mul_transpose,
    exWf_mul_transpose]
  module

theorem exWh_mul_exZ : exWh * exZ = exW₁ := by
  rw [exWh, exZ, exW₁, fromCols_mul_fromBlocks]
  simp

theorem posSemidef_one_sub_exZ_mul_transpose : (1 - exZ * exZᵀ).PosSemidef := by
  have e : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - exZ * exZᵀ = fromBlocks 0 0 0 1 := by
    rw [exZ, fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg,
      fromBlocks_neg, fromBlocks_add]
    simp
  rw [e]
  exact StackedTruncation.posSemidef_fromBlocks_diag Matrix.PosSemidef.zero
    Matrix.PosSemidef.one

theorem rank_exZ_le : exZ.rank ≤ 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ,
      u = fromRows (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) := ⟨_, rfl⟩
  have e : exZ = u * uᵀ := by
    rw [hu, transpose_fromRows, fromRows_mul_fromCols, exZ]
    simp
  rw [e]
  exact (Matrix.rank_mul_le_right _ _).trans (uᵀ.rank_le_card_height.trans (by simp))

theorem norm_exB_mul_transpose : ‖exB * exBᵀ‖ = 2 := by
  have h : ‖exB * exBᵀ‖ ^ 2 = 4 := by
    rw [Frobenius.norm_sq_eq_sum, exB_mul_transpose]
    simp [Fintype.sum_sum_type]
    norm_num
  nlinarith [norm_nonneg (exB * exBᵀ)]

theorem norm_exWh_sub_le : ‖exWh * exWhᵀ - exW₁ * exW₁ᵀ‖ ≤ 1 / 2 := by
  rw [exWh_mul_transpose, exW₁_mul_transpose, add_sub_cancel_left, norm_smul,
    norm_exB_mul_transpose, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  norm_num

theorem half_lt_norm_exWh : 1 / 2 < ‖exWh * exWhᵀ‖ := by
  have h : ‖exWh * exWhᵀ‖ ^ 2 = 17 / 4 := by
    rw [Frobenius.norm_sq_eq_sum, exWh_mul_transpose, exA_mul_transpose, exB_mul_transpose]
    simp [Fintype.sum_sum_type]
    norm_num
  nlinarith [norm_nonneg (exWh * exWhᵀ)]

/-- A matrix of Frobenius norm larger than `θ ≥ 0` has `θ`-rank at least one. -/
private theorem one_le_epsRank_of_lt_norm {p q : Type*} [Fintype p] [Fintype q]
    {M : Matrix p q ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hM : θ < ‖M‖) : 1 ≤ epsRank θ M := by
  classical
  by_contra hc
  have hd : distLR 0 M ≤ θ := (epsRank_le_iff hθ).mp (by omega)
  have hle : ‖M‖ ≤ distLR 0 M := by
    rw [le_distLR_iff]
    intro Z hZ
    have h0 : Z.rank = 0 := Nat.le_zero.mp hZ
    rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    have hZ0 : Z = 0 := by
      ext i j
      have := congrArg (fun g => g (Pi.single j 1) i) h0
      simpa [Matrix.mulVec_single] using this
    rw [hZ0, sub_zero]
  linarith

theorem exW₁_block : exW₁.toRows₁ * exW₁.toRows₂ᵀ = 1 := by
  rw [← StackedTruncation.toBlocks₁₂_mul_transpose, exW₁_mul_transpose, exA_mul_transpose,
    toBlocks_fromBlocks₁₂]

theorem exWh_block_ne : (exWh * exWhᵀ).toBlocks₁₂ ≠ exW₁.toRows₁ * exW₁.toRows₂ᵀ := by
  rw [exWh_mul_transpose, exA_mul_transpose, exB_mul_transpose, fromBlocks_smul, fromBlocks_add,
    toBlocks_fromBlocks₁₂, exW₁_block]
  intro h0
  have := congrFun (congrFun h0 0) 0
  norm_num at this

/-- With `P = -1`, `Q = 3` and the shift `σ = 2`, the lifted operator is the identity. -/
theorem shifted_lift_eq_one : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
    = fromBlocks ((-1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) + (2 : ℝ) • 1) 0 0
      ((3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) - (2 : ℝ) • 1) := by
  rw [← fromBlocks_one]
  congr 1 <;> module

/-- The lifted backward Euler run of the examples: `exW₀ exW₀ᵀ`, then `exWh exWhᵀ`. -/
def exX (j : ℕ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  if j = 0 then exW₀ * exW₀ᵀ else exWh * exWhᵀ

/-- The stacked factors of the truncated run of the examples: `exW₀`, then `exW₁`. -/
def exW (j : ℕ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ := if j = 0 then exW₀ else exW₁

/-- The right-hand side `t W₀ W₀ᵀ + t⁻¹ (P W₀)(P W₀)ᵀ` with `P = 1` and `t = 1`. -/
def exF₀ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  (1 : ℝ) • (exW₀ * exW₀ᵀ) + (1 : ℝ)⁻¹ • (1 * exW₀ * (1 * exW₀)ᵀ)

/-- The stationary solution `S = W₀ W₀ᵀ + Wf Wfᵀ / 2` of `S + S = F₀ + Wf Wfᵀ`. -/
def exS : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  exW₀ * exW₀ᵀ + (1 / 2 : ℝ) • (exWf * exWfᵀ)

theorem exX_zero : exX 0 = exW₀ * exW₀ᵀ := by simp [exX]

theorem exX_one : exX 1 = exWh * exWhᵀ := by simp [exX]

theorem exW_zero : exW 0 = exW₀ := by simp [exW]

theorem exW_one : exW 1 = exW₁ := by simp [exW]

theorem posSemidef_one_sub_one_smul :
    ((1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) - (1 : ℝ) • 1).PosSemidef := by
  simpa using Matrix.PosSemidef.zero

theorem exF₀_eq : exF₀ = (2 : ℝ) • (exW₀ * exW₀ᵀ) := by
  rw [exF₀, inv_one, one_smul, one_smul, Matrix.one_mul, two_smul]

theorem posSemidef_exF₀ : exF₀.PosSemidef := by
  rw [exF₀_eq]
  exact (StationaryDomination.posSemidef_mul_transpose_self _).smul (by norm_num)

theorem exS_lyapunov : 1 * exS + exS * 1 = exF₀ + exWf * exWfᵀ := by
  rw [Matrix.one_mul, Matrix.mul_one, exF₀_eq, exS]
  module

theorem posSemidef_exF₀_sub : (exF₀ - (1 * exX 0 + exX 0 * 1)).PosSemidef := by
  rw [exX_zero]
  exact (StationaryDomination.posSemidef_sub_lyapunov_of_smul_add_inv_smul
    (P := (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)) transpose_one exW₀ one_pos).1

theorem posSemidef_exS_sub : (exS - exX 0).PosSemidef :=
  StationaryDomination.posSemidef_sub_of_lyapunov_le posSemidef_one_sub_one_smul one_pos
    (StationaryDomination.posSemidef_mul_transpose_self exWf) exS_lyapunov posSemidef_exF₀_sub

theorem exX_step : ∀ j < 1, exX (j + 1) + (4 : ℝ) • (1 * exX (j + 1) + exX (j + 1) * 1)
    = exX j + (4 : ℝ) • (exWf * exWfᵀ) := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [zero_add, exX_one, exX_zero]
  exact exWh_step

theorem exWh_step_of_lt : ∀ j < 1,
    exWh * exWhᵀ + (4 : ℝ) • (1 * (exWh * exWhᵀ) + exWh * exWhᵀ * 1)
      = exW j * (exW j)ᵀ + (4 : ℝ) • (exWf * exWfᵀ) := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [exW_zero]
  exact exWh_step

theorem posSemidef_exX_sub_exW_zero : (exX 0 - exW 0 * (exW 0)ᵀ).PosSemidef := by
  rw [exX_zero, exW_zero, sub_self]
  exact Matrix.PosSemidef.zero

theorem exW_succ : ∀ j < 1, exW (j + 1) = exWh * exZ := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [zero_add, exW_one, exWh_mul_exZ]

theorem exZ_rank_le : ∀ j < 1, exZ.rank ≤ epsRank (1 / 2) (exWh * exWhᵀ) :=
  fun _ _ => rank_exZ_le.trans (one_le_epsRank_of_lt_norm (by norm_num) half_lt_norm_exWh)

theorem posSemidef_exWh_sub_exW :
    ∀ j < 1, (exWh * exWhᵀ - exW (j + 1) * (exW (j + 1))ᵀ).PosSemidef := by
  intro j hj
  rw [exW_succ j hj]
  exact StackedTruncation.posSemidef_mul_transpose_sub_mul_transpose _
    posSemidef_one_sub_exZ_mul_transpose

theorem rank_exW_le :
    ∀ j < 1, (exW (j + 1) * (exW (j + 1))ᵀ).rank ≤ epsRank (1 / 2) (exWh * exWhᵀ) := by
  intro j hj
  rw [exW_succ j hj]
  exact (StackedTruncation.rank_mul_mul_transpose_le _ _).trans (exZ_rank_le j hj)

theorem norm_exWh_sub_exW_le :
    ∀ j < 1, ‖exWh * exWhᵀ - exW (j + 1) * (exW (j + 1))ᵀ‖ ≤ 1 / 2 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [zero_add, exW_one]
  exact norm_exWh_sub_le

theorem norm_exX_sub_exW_zero_le : ‖exX 0 - exW 0 * (exW 0)ᵀ‖ ≤ ((0 : ℕ) : ℝ) / 2 := by
  rw [exX_zero, exW_zero, sub_self, norm_zero]
  simp

theorem exE_step : ∀ j : ℕ, j < 1 →
    (j : ℝ) / 2 / (1 + 4 * (-1 + 3)) + 1 / 2 ≤ ((j + 1 : ℕ) : ℝ) / 2 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  norm_num

/-- The instance is not trivial: the truncation changes the iterate, the truncated iterate has
rank one, and its off-diagonal block `L₁ R₁ᵀ = 1` differs from the off-diagonal block `3/4` of
the lifted run. Also, `P = -1` is not positive semidefinite. -/
example : exX 1 ≠ exW 1 * (exW 1)ᵀ ∧ 0 < (exW 1 * (exW 1)ᵀ).rank ∧
    (exX 1).toBlocks₁₂ ≠ (exW 1).toRows₁ * (exW 1).toRows₂ᵀ ∧
    0 < ((exW 1).toRows₁ * (exW 1).toRows₂ᵀ).rank ∧
    ¬ ((-1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef := by
  have hb : (exX 1).toBlocks₁₂ ≠ (exW 1).toRows₁ * (exW 1).toRows₂ᵀ := by
    rw [exX_one, exW_one]
    exact exWh_block_ne
  have hr : 0 < ((exW 1).toRows₁ * (exW 1).toRows₂ᵀ).rank := by
    rw [exW_one, exW₁_block, Matrix.rank_one]
    simp
  refine ⟨fun h0 => hb ?_, ?_, hb, hr, fun hP => ?_⟩
  · rw [h0, StackedTruncation.toBlocks₁₂_mul_transpose]
  · have h1 := StackedTruncation.rank_toBlocks₁₂_le (exW 1 * (exW 1)ᵀ)
    rw [StackedTruncation.toBlocks₁₂_mul_transpose] at h1
    omega
  · have h0 := hP.diag_nonneg (i := 0)
    norm_num at h0

/-- `StationaryDomination.posSemidef_of_lyapunov`, `StationaryDomination.existsUnique_lyapunov`
and `StationaryDomination.exists_lyapunov_posSemidef_sub` on the instance (`P = 1`, `c = t = 1`):
the stationary solution is positive semidefinite, unique, and dominates the start. -/
example : exS.PosSemidef ∧ (∃! S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ,
      1 * S + S * 1 = exF₀ + exWf * exWfᵀ) ∧
    ∃ S : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ, (S - exW₀ * exW₀ᵀ).PosSemidef := by
  refine ⟨StationaryDomination.posSemidef_of_lyapunov posSemidef_one_sub_one_smul one_pos
      (posSemidef_exF₀.add (StationaryDomination.posSemidef_mul_transpose_self exWf)) exS_lyapunov,
    StationaryDomination.existsUnique_lyapunov posSemidef_one_sub_one_smul one_pos _, ?_⟩
  obtain ⟨S, -, hS, -⟩ := StationaryDomination.exists_lyapunov_posSemidef_sub
    posSemidef_one_sub_one_smul one_pos one_pos exW₀ exWf
  exact ⟨S, hS⟩

/-- `StationaryDomination.posSemidef_sub_of_lyapunov_run` and
`StationaryDomination.rank_le_epsRank_of_truncated_lyapunov_run_of_stationary` on the instance
(`P = 1`, `h = 4`, `θ = 1/2`, `F = exWf exWfᵀ`): the truncated iterate of rank one lies below
the run, the run lies below `S`, and `rank_{1/2}(S) ≥ 1`. -/
example : (∀ j ≤ 1, (exS - exX j).PosSemidef) ∧ (exX 1 - exW 1 * (exW 1)ᵀ).PosSemidef ∧
    (exS - exX 1).PosSemidef ∧ (exW 1 * (exW 1)ᵀ).rank ≤ epsRank (1 / 2) exS := by
  have h := StationaryDomination.rank_le_epsRank_of_truncated_lyapunov_run_of_stationary
    (Y := fun j => exW j * (exW j)ᵀ) (Yh := fun _ => exWh * exWhᵀ) Matrix.PosSemidef.one
    (StationaryDomination.posSemidef_mul_transpose_self exWf) posSemidef_exF₀ (by norm_num)
    (by norm_num) exS_lyapunov exX_step exWh_step_of_lt
    (StationaryDomination.posSemidef_mul_transpose_self (exW 0)) posSemidef_exX_sub_exW_zero
    posSemidef_exS_sub (fun j _ => StationaryDomination.posSemidef_mul_transpose_self (exW (j + 1)))
    posSemidef_exWh_sub_exW rank_exW_le 0 one_pos
  exact ⟨StationaryDomination.posSemidef_sub_of_lyapunov_run Matrix.PosSemidef.one posSemidef_exF₀
    (by norm_num) exS_lyapunov exX_step posSemidef_exS_sub, h⟩

/-- `StationaryDomination.rank_le_epsRank_of_stacked_sylvester_run_of_stationary` on the instance
with `P = Q = 1` on `1 × 1` matrices (the lifted operator `diag(1, 1)`). -/
example : ((exW 1).toRows₁ * (exW 1).toRows₂ᵀ).rank ≤ epsRank (1 / 2) exS := by
  have h := StationaryDomination.rank_le_epsRank_of_stacked_sylvester_run_of_stationary
    (P := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Q := 1) (X := exX) (W := exW) (Wh := fun _ => exWh)
    (Z := fun _ => exZ) (Wf := exWf) (S := exS) (F₀ := exF₀) (h := 4) (θ := 1 / 2) (N := 1)
    Matrix.PosSemidef.one Matrix.PosSemidef.one (by norm_num) (by norm_num)
    (by simpa only [fromBlocks_one] using exX_step)
    (by simpa only [fromBlocks_one] using exWh_step_of_lt) posSemidef_exX_sub_exW_zero exW_succ
    (fun _ _ => posSemidef_one_sub_exZ_mul_transpose) exZ_rank_le posSemidef_exF₀
    (by simpa only [fromBlocks_one] using exS_lyapunov) posSemidef_exS_sub
  exact (h 0 one_pos).2.2

/-- `StationaryDomination.rank_le_epsRank_and_norm_sub_le_of_shifted_lift` on the instance: the
Sylvester problem with `P = -1` (not positive semidefinite) and `Q = 3`, `P ⪰ α = -1`,
`Q ⪰ β = 3`, `a = 2`, `σ = 2` (the lifted operator is the identity), `[G; H] = (3/4)[1; -1]`,
`h = 4`, `θ = 1/2`, `E_j = j / 2`. The computed iterate has `rank (L₁ R₁ᵀ) ≤ rank_{1/2}(S)` and
`√2 ‖X₁ - L₁ R₁ᵀ‖ ≤ 1/2` (in fact `X₁ = 3/4`, `L₁ R₁ᵀ = 1`). -/
example : ((exW 1).toRows₁ * (exW 1).toRows₂ᵀ).rank ≤ epsRank (1 / 2) exS ∧
    Real.sqrt 2 * ‖(exX 1).toBlocks₁₂ - (exW 1).toRows₁ * (exW 1).toRows₂ᵀ‖ ≤ 1 / 2 := by
  have h := StationaryDomination.rank_le_epsRank_and_norm_sub_le_of_shifted_lift
    (P := (-1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Q := (3 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (α := -1) (β := 3) (σ := 2) (PQ := 1) (X := exX) (W := exW) (Wh := fun _ => exWh)
    (Z := fun _ => exZ) (Wf := exWf) (S := exS) (F₀ := exF₀) (h := 4) (θ := 1 / 2) (N := 1)
    (E := fun j => (j : ℝ) / 2)
    (by rw [sub_self]; exact Matrix.PosSemidef.zero)
    (by rw [sub_self]; exact Matrix.PosSemidef.zero)
    (by norm_num) (by norm_num) shifted_lift_eq_one (by norm_num) (by norm_num) exX_step
    exWh_step_of_lt posSemidef_exX_sub_exW_zero exW_succ
    (fun _ _ => posSemidef_one_sub_exZ_mul_transpose) exZ_rank_le norm_exWh_sub_exW_le
    posSemidef_exF₀ exS_lyapunov posSemidef_exS_sub norm_exX_sub_exW_zero_le exE_step
  refine ⟨(h.1 0 one_pos).2.2, ?_⟩
  simpa using h.2 1 le_rfl

/-! #### An instance with an operator that is not a multiple of the identity

`P = diag(1, 2, 3)`, `c = 1`, the start factor `W₀ = [1; 1; 1]`, `t = 2` and the forcing factor
`Wf = [0; 0; 1]`. Here `F₀ - (P X₀ + X₀ P) = (1/2) (2 W₀ - P W₀)(2 W₀ - P W₀)ᵀ` is not zero, and
the bound `rank F₀ ≤ 2` is below the dimension `3`. -/

/-- The diagonal operator `diag(1, 2, 3)`. -/
def exP₃ : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 2, 3]

/-- The start factor `[1; 1; 1]`. -/
def exV₃ : Matrix (Fin 3) (Fin 1) ℝ := !![1; 1; 1]

/-- The forcing factor `[0; 0; 1]`. -/
def exU₃ : Matrix (Fin 3) (Fin 1) ℝ := !![0; 0; 1]

/-- The stationary solution for `P = diag(1, 2, 3)`, `t = 2`, `W₀ = [1; 1; 1]`, `Wf = [0; 0; 1]`. -/
def exS₃ : Matrix (Fin 3) (Fin 3) ℝ := !![5 / 4, 1, 7 / 8; 1, 1, 1; 7 / 8, 1, 5 / 4]

theorem exP₃_transpose : exP₃ᵀ = exP₃ := by
  rw [exP₃, diagonal_transpose]

theorem posSemidef_exP₃_sub : (exP₃ - (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  have e : exP₃ - (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = diagonal ![0, 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [exP₃, Matrix.one_apply, Matrix.diagonal_apply]
  rw [e, posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem exS₃_lyapunov : exP₃ * exS₃ + exS₃ * exP₃
    = (2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ) + exU₃ * exU₃ᵀ := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [exP₃, exS₃, exV₃, exU₃, Matrix.diagonal_apply]

/-- `StationaryDomination.posSemidef_sub_lyapunov_of_smul_add_inv_smul` on `P = diag(1, 2, 3)`,
`W = [1; 1; 1]` and `t = 2`: `P` is not a multiple of the identity, the difference
`F₀ - (P W Wᵀ + W Wᵀ P)` is positive semidefinite and not zero, and `rank F₀ ≤ 2` in
dimension `3`. -/
example : (¬ ∃ s : ℝ, exP₃ = s • 1) ∧
    (2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ)
      - (exP₃ * (exV₃ * exV₃ᵀ) + exV₃ * exV₃ᵀ * exP₃) ≠ 0 ∧
    ((2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ)
      - (exP₃ * (exV₃ * exV₃ᵀ) + exV₃ * exV₃ᵀ * exP₃)).PosSemidef ∧
    ((2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ)).rank ≤ 2 := by
  obtain ⟨hd, hr⟩ := StationaryDomination.posSemidef_sub_lyapunov_of_smul_add_inv_smul
    exP₃_transpose exV₃ (t := 2) two_pos
  refine ⟨?_, ?_, hd, hr.trans (by simp)⟩
  · rintro ⟨s, hs⟩
    have h0 := congrFun (congrFun hs 0) 0
    have h1 := congrFun (congrFun hs 1) 1
    norm_num [exP₃] at h0 h1
    linarith
  · intro h0
    have h1 := congrFun (congrFun h0 0) 0
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.zero_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      smul_eq_mul] at h1
    norm_num [exP₃, exV₃, Matrix.diagonal_apply] at h1

/-- `StationaryDomination.posSemidef_sub_of_lyapunov_le`,
`StationaryDomination.posSemidef_of_lyapunov`, `StationaryDomination.existsUnique_lyapunov` and
`StationaryDomination.exists_lyapunov_posSemidef_sub` on the same instance with `c = 1`: the
stationary solution `S = [[5/4, 1, 7/8], [1, 1, 1], [7/8, 1, 5/4]]` is positive semidefinite and
unique, it dominates the start `W₀ W₀ᵀ` with `S - W₀ W₀ᵀ ≠ 0`, and it is the majorant of
`exists_lyapunov_posSemidef_sub`. -/
example : exS₃.PosSemidef ∧ (exS₃ - exV₃ * exV₃ᵀ).PosSemidef ∧ exS₃ - exV₃ * exV₃ᵀ ≠ 0 ∧
    (∃! S : Matrix (Fin 3) (Fin 3) ℝ, exP₃ * S + S * exP₃
      = (2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ) + exU₃ * exU₃ᵀ) ∧
    ∃ S : Matrix (Fin 3) (Fin 3) ℝ, S = exS₃ ∧ (S - exV₃ * exV₃ᵀ).PosSemidef := by
  have hu := StationaryDomination.existsUnique_lyapunov posSemidef_exP₃_sub one_pos
    ((2 : ℝ) • (exV₃ * exV₃ᵀ) + (2 : ℝ)⁻¹ • (exP₃ * exV₃ * (exP₃ * exV₃)ᵀ) + exU₃ * exU₃ᵀ)
  obtain ⟨S, hS, hdom, hF₀, -⟩ := StationaryDomination.exists_lyapunov_posSemidef_sub
    posSemidef_exP₃_sub one_pos two_pos exV₃ exU₃
  have hle := StationaryDomination.posSemidef_sub_of_lyapunov_le posSemidef_exP₃_sub one_pos
    (StationaryDomination.posSemidef_mul_transpose_self exU₃) exS₃_lyapunov
    (StationaryDomination.posSemidef_sub_lyapunov_of_smul_add_inv_smul exP₃_transpose exV₃
      two_pos).1
  refine ⟨StationaryDomination.posSemidef_of_lyapunov posSemidef_exP₃_sub one_pos
      (hF₀.add (StationaryDomination.posSemidef_mul_transpose_self exU₃)) exS₃_lyapunov, hle,
    fun h0 => ?_, hu, S, hu.unique hS exS₃_lyapunov, hdom⟩
  have h1 := congrFun (congrFun h0 0) 0
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero] at h1
  norm_num [exS₃, exV₃] at h1

/-! #### Domination with a forcing that is not positive semidefinite

`P = diag(1, 2)`, `F = [[1, 1], [1, -1]]`, `S = 1`, `F₀ = 2 P - F = G Gᵀ` with
`G = [[1, 0], [-1, 2]]`, step size `h = 1` and `X₀ = 0`. The first iterate
`X₁ = [[1/3, 1/4], [1/4, -1/5]]` is not positive semidefinite, and still `X₁ ⪯ S`. -/

/-- The diagonal operator `diag(1, 2)`. -/
def exP₂ : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, 2]

/-- The forcing `[[1, 1], [1, -1]]`, neither positive nor negative semidefinite. -/
def exF₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]

/-- A factor of `F₀ = 2 diag(1, 2) - F`. -/
def exG₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -1, 2]

/-- The backward Euler run from `0` with step size `1` for `P = diag(1, 2)` and the forcing
`exF₂`: `0`, then `[[1/3, 1/4], [1/4, -1/5]]`. -/
def exX₂ (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := if j = 0 then 0 else !![1 / 3, 1 / 4; 1 / 4, -1 / 5]

theorem posSemidef_exP₂ : exP₂.PosSemidef := by
  rw [exP₂, posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

theorem exP₂_lyapunov_one : exP₂ * 1 + 1 * exP₂ = exG₂ * exG₂ᵀ + exF₂ := by
  ext i j
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;> fin_cases j <;> norm_num [exP₂, exG₂, exF₂, Matrix.diagonal_apply]

theorem exX₂_step : ∀ j < 1, exX₂ (j + 1) + (1 : ℝ) • (exP₂ * exX₂ (j + 1) + exX₂ (j + 1) * exP₂)
    = exX₂ j + (1 : ℝ) • exF₂ := by
  intro j hj
  obtain rfl : j = 0 := by omega
  ext i k
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, smul_eq_mul]
  fin_cases i <;> fin_cases k <;> norm_num [exX₂, exP₂, exF₂, Matrix.diagonal_apply]

/-- `StationaryDomination.posSemidef_sub_of_lyapunov_run` with a forcing that is neither positive
nor negative semidefinite: the iterate `X₁` leaves the positive semidefinite cone, and still
`X_j ⪯ S = 1` for `j ≤ 1`. -/
example : ¬ exF₂.PosSemidef ∧ ¬ (-exF₂).PosSemidef ∧ ¬ (exX₂ 1).PosSemidef ∧
    ∀ j ≤ 1, (1 - exX₂ j).PosSemidef := by
  refine ⟨fun hF => ?_, fun hF => ?_, fun hX => ?_,
    StationaryDomination.posSemidef_sub_of_lyapunov_run posSemidef_exP₂
      (StationaryDomination.posSemidef_mul_transpose_self exG₂) zero_le_one exP₂_lyapunov_one
      exX₂_step ?_⟩
  · have h0 := hF.diag_nonneg (i := 1)
    norm_num [exF₂] at h0
  · have h0 := hF.diag_nonneg (i := 0)
    norm_num [exF₂] at h0
  · have h0 := hX.diag_nonneg (i := 1)
    norm_num [exX₂] at h0
  · rw [show exX₂ 0 = 0 by simp [exX₂], sub_zero]
    exact Matrix.PosSemidef.one

end

end LeanDLRA.StationaryDominationExample

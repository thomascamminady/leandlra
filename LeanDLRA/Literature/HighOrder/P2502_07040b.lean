import LeanDLRA.Classical.EckartYoung
import LeanDLRA.LinearAlgebra.Factorization.Defs
import LeanDLRA.Foundations.Projector
import LeanDLRA.Matrix.Frobenius
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors

/-!
# Results of arXiv 2502.07040: truncation error of the RK-BUG integrator

This module formalises the Runge–Kutta BUG integrator of Nobile–Riffaud (Algorithm 2) concretely on
real `n × m` matrices in the Frobenius norm (`IsRKBUGStep`, `IsRKBUGSolution`: orthonormal bases of
the paper's concatenated ranges, Galerkin core, best rank-`r` approximation; solutions exist for all
data by `exists_rkbug_solution`) and proves **Proposition 4**: under Assumption 1 alone, the
truncation errors satisfy (25)–(26) with `B` the supremum (20) over the neighbourhood `𝓥_r` of (19)
(`truncation_error`, with one constant `truncation_error_gamma`, for the library's truncated SVD
`truncation_error_truncation`; vanishing at full rank is `gammaBar_eq_zero`). That the stages lie in
`𝓥_r` is derived, not assumed (`stage_mem_nbhdV`), from **Lemma 1** (`IsRKBUGStep.stage_bound`),
**Lemma 2** (`IsRKBUGStep.final_bound`) and **Proposition 2** (`IsRKBUGSolution.norm_sub_le`), with
the paper's recursive constants. Differences from the paper: (a) Proposition 4 leaves `γ̄_r`
unspecified and computes it only for (25), as `√(min {n, m, 2 r s} - r) C_b B`; the proof of (26) is
omitted ("the same arguments"), and those arguments give `∑ⱼ |a_{ij}|` in place of `C_b`. The
constant of (25) cannot be reused for (26) (`stage_bound_false_with_Cb`, Kutta's third-order
method), so `truncation_error_gamma` takes `γ̄_r` with `max {C_b, maxᵢ ∑ⱼ |a_{ij}|}`, and
Proposition 4 as printed holds; (b) the proof uses Eckart–Young in the form `‖Ŷ - 𝓡(Ŷ)‖ ≤ ‖Ŷ - Y_k‖`
instead of Weyl's inequalities, and `rank Ŷ ≤ min {n, m, 2 r s}` only for the case of zero error, so
the root can be dropped when it is nonzero (`truncation_error_sharp`); (c) `𝓡(Ŷ)` is any best
rank-`r` approximation, which the truncated SVD of `Ŝ` provides, so more trajectories are covered
than in Algorithm 2; `Û`, `V̂` may have different numbers of columns; (d) `𝓥_r` uses `rank ≤ r`, see
`nbhdV`; (e) `0 ≤ c_i ≤ 1` is assumed so that the stage times lie in `[0, T]`, where Assumption 1
lives; (f) if `K̃₀ = 0`, Lean's `x / 0 = 0` is consistent with Proposition 2, see there. Proposition
1 on the exact solution is not formalised: it only serves to put the exact solution into `𝓥_r`, and
here `R₁` just enlarges the set in (20).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2502_07040

open LeanDLRA.EckartYoung Module

variable {n m r s : ℕ}

/-! ### The RK-BUG integrator (Algorithm 2) -/

/-- An explicit Runge–Kutta tableau `(a_{ij}, b_i, c_i)` with `s` stages, eq. (10). -/
structure ExplicitRK (s : ℕ) where
  /-- The Runge–Kutta matrix. -/
  a : Fin s → Fin s → ℝ
  /-- The weights. -/
  b : Fin s → ℝ
  /-- The nodes. -/
  c : Fin s → ℝ
  /-- Explicitness: `a_{ij} = 0` for `i ≤ j`. -/
  a_eq_zero : ∀ i j, i ≤ j → a i j = 0

/-- A low-rank matrix `U S Vᵀ` with `r × r` core and orthonormal `n × r` and `m × r` bases, eq. (2).
As the algorithm can produce zero singular values, `S` need not be invertible. -/
structure LowRank (n m r : ℕ) where
  /-- The left basis. -/
  U : Matrix (Fin n) (Fin r) ℝ
  /-- The core. -/
  S : Matrix (Fin r) (Fin r) ℝ
  /-- The right basis. -/
  V : Matrix (Fin m) (Fin r) ℝ
  U_orth : Uᵀ * U = 1
  V_orth : Vᵀ * V = 1

/-- The matrix `U S Vᵀ`. -/
def LowRank.mat (Y : LowRank n m r) : Matrix (Fin n) (Fin m) ℝ := Y.U * Y.S * Y.Vᵀ

/-- `Q = orth(W)`: the columns of `Q` are an orthonormal basis of the subspace `W`. -/
structure IsOrthOf {d p : ℕ} (Q : Matrix (Fin d) (Fin p) ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Prop where
  orthonormal : Qᵀ * Q = 1
  colSpan_eq : colSpan Q = W

/-- The range of the concatenation `[U₀, w₁ U₁, w₁ G₁, …, w_s U_s, w_s G_s]` (the term `w₁ U₁`,
which the paper removes, is redundant as `U₁ = U₀`). -/
def augSpace {d : ℕ} (U₀ : Matrix (Fin d) (Fin r) ℝ) (w : Fin s → ℝ)
    (U G : Fin s → Matrix (Fin d) (Fin r) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  colSpan U₀ ⊔ ⨆ i, (colSpan (w i • U i) ⊔ colSpan (w i • G i))

/-! "`B` is a best approximation of `A` among the matrices of rank at most `r`", that is, a value of
the retraction `𝓡_{𝓜_r}(A)` (the `r`-truncated SVD of `A`), is the core
`IsBestLowRankApprox r A B`; the local `IsBestRankApprox` of an earlier version of this file was
the same definition (unification batch C4). -/

/-- One BUG update with weights `w` (lines 6–10 of Algorithm 2 with `w = a_{i+1,·}` and lines 14–18
with `w = b`): the augmented bases `Û`, `V̂` are orthonormal bases of the ranges of
`[U_k, w₁ F₁ V₁, …, w_s U_s, w_s F_s V_s]` and `[V_k, w₁ F₁ᵀ U₁, …, w_s V_s, w_s F_sᵀ U_s]`,
`Ŝ = Ûᵀ (Y_k + h ∑ⱼ wⱼ Fⱼ) V̂`, `Ŷ = Û Ŝ V̂ᵀ`, and `Ynew` is the `r`-truncated SVD of `Ŷ`.
The numbers of columns `p`, `q` of `Û`, `V̂` are the dimensions of these ranges, so `Ŝ` may be
rectangular. -/
def IsAugmentedUpdate (Yk : LowRank n m r) (Ys : Fin s → LowRank n m r)
    (Fs : Fin s → Matrix (Fin n) (Fin m) ℝ) (h : ℝ) (w : Fin s → ℝ)
    (Yhat : Matrix (Fin n) (Fin m) ℝ) (Ynew : LowRank n m r) : Prop :=
  ∃ (p q : ℕ) (Uh : Matrix (Fin n) (Fin p) ℝ) (Vh : Matrix (Fin m) (Fin q) ℝ),
    IsOrthOf Uh (augSpace Yk.U w (fun i => (Ys i).U) fun i => Fs i * (Ys i).V) ∧
    IsOrthOf Vh (augSpace Yk.V w (fun i => (Ys i).V) fun i => (Fs i)ᵀ * (Ys i).U) ∧
    Yhat = Uh * (Uhᵀ * (Yk.mat + h • ∑ j, w j • Fs j) * Vh) * Vhᵀ ∧
    IsBestLowRankApprox r Yhat Ynew.mat

/-- One step of the **RK-BUG integrator**, Algorithm 2, from `Yk` at time `t`: the stages `Ys i`
with `F_i = F (t + c_i h) (Ys i)`, their augmented solutions `Yhs i`, the augmented solution `Yh`
and the result `Ynext`. Stage `i` depends on stage `j` only if `a_{ij} ≠ 0`, hence only if
`j < i`. -/
structure IsRKBUGStep (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (tab : ExplicitRK s) (h t : ℝ) (Yk : LowRank n m r) (Ys : Fin s → LowRank n m r)
    (Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ) (Yh : Matrix (Fin n) (Fin m) ℝ)
    (Ynext : LowRank n m r) : Prop where
  first : ∀ i : Fin s, (i : ℕ) = 0 → Ys i = Yk
  stage : ∀ i : Fin s, (i : ℕ) ≠ 0 →
    IsAugmentedUpdate Yk Ys (fun j => F (t + tab.c j * h) (Ys j).mat) h (tab.a i) (Yhs i) (Ys i)
  final : IsAugmentedUpdate Yk Ys (fun j => F (t + tab.c j * h) (Ys j).mat) h tab.b Yh Ynext

/-- `N` steps of Algorithm 2 on the grid `t_k = k h`. -/
def IsRKBUGSolution (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (tab : ExplicitRK s) (h : ℝ) (N : ℕ) (Y : ℕ → LowRank n m r)
    (Ys : ℕ → Fin s → LowRank n m r) (Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ)
    (Yh : ℕ → Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ k < N, IsRKBUGStep F tab h (k * h) (Y k) (Ys k) (Yhs k) (Yh k) (Y (k + 1))

/-! ### One update -/

lemma LowRank.rank_mat_le (Y : LowRank n m r) : Y.mat.rank ≤ r :=
  rank_mul_mul_transpose_le _ _ _

lemma capture_of_colSpan_le {d p : ℕ} {κ : Type*} {Q : Matrix (Fin d) (Fin p) ℝ}
    (hQ : Qᵀ * Q = 1) {X : Matrix (Fin d) κ ℝ} (h : colSpan X ≤ colSpan Q) : Q * Qᵀ * X = X := by
  obtain ⟨C, hC⟩ := exists_eq_mul_of_col_mem_span (u := fun j => WithLp.toLp 2 (Q.col j)) (X := X)
    fun j => h (toLp_col_mem_colSpan X j)
  exact mul_transpose_mul_eq_of_eq_mul hQ hC

/-- **Bridge.** An orthonormal basis `Q` of a subspace `W` captures every matrix whose columns lie
in `W`: `Q` is an orthonormal frame capturing `X` in the sense of the core
`Matrix.IsOrthCapture`. -/
theorem IsOrthOf.isOrthCapture {d p : ℕ} {κ : Type*} {Q : Matrix (Fin d) (Fin p) ℝ}
    {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))} (h : IsOrthOf Q W) {X : Matrix (Fin d) κ ℝ}
    (hX : colSpan X ≤ W) : Matrix.IsOrthCapture Q X :=
  ⟨h.orthonormal, capture_of_colSpan_le h.orthonormal (h.colSpan_eq ▸ hX)⟩

lemma colSpan_smul_le {d : ℕ} {κ : Type*} (c : ℝ) (A : Matrix (Fin d) κ ℝ) :
    colSpan (c • A) ≤ colSpan A := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  have : WithLp.toLp 2 ((c • A).col j) = c • WithLp.toLp 2 (A.col j) := by
    ext i; simp
  rw [SetLike.mem_coe]
  simp only
  rw [this]
  exact Submodule.smul_mem _ _ (toLp_col_mem_colSpan A j)

lemma finrank_finset_sup_le {d : ℕ} {ι : Type*} (T : Finset ι)
    (P : ι → Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    finrank ℝ ↥(T.sup P) ≤ ∑ i ∈ T, finrank ℝ (P i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

lemma finrank_colSpan_le {d : ℕ} (A : Matrix (Fin d) (Fin r) ℝ) : finrank ℝ (colSpan A) ≤ r := by
  rw [finrank_colSpan]; simpa using A.rank_le_card_width

/-- The augmented rank is at most `2 r s` (Sec. 2.4 of the paper): the columns of
`[U₀, w₁ G₁, w₂ U₂, w₂ G₂, …, w_s U_s, w_s G_s]` are `r + r + 2 r (s - 1)` many. -/
theorem finrank_augSpace_le {d : ℕ} (hs : 0 < s) (U₀ : Matrix (Fin d) (Fin r) ℝ) (w : Fin s → ℝ)
    (U G : Fin s → Matrix (Fin d) (Fin r) ℝ) (hU : U ⟨0, hs⟩ = U₀) :
    finrank ℝ (augSpace U₀ w U G) ≤ 2 * r * s := by
  classical
  set i₀ : Fin s := ⟨0, hs⟩ with hi₀
  let Q : Fin s → Submodule ℝ (EuclideanSpace ℝ (Fin d)) := fun i =>
    if i = i₀ then colSpan (w i • G i) else colSpan (w i • U i) ⊔ colSpan (w i • G i)
  have hle : augSpace U₀ w U G ≤ colSpan U₀ ⊔ univ.sup Q := by
    refine sup_le le_sup_left (iSup_le fun i => ?_)
    have hQ : Q i ≤ univ.sup Q := Finset.le_sup (mem_univ i)
    by_cases hi : i = i₀
    · subst hi
      have hQ' : colSpan (w i₀ • G i₀) ≤ univ.sup Q := by simpa [Q] using hQ
      refine sup_le ?_ (hQ'.trans le_sup_right)
      rw [hU]
      exact (colSpan_smul_le _ _).trans le_sup_left
    · have hQ' : colSpan (w i • U i) ⊔ colSpan (w i • G i) ≤ univ.sup Q := by
        simpa [Q, hi] using hQ
      exact hQ'.trans le_sup_right
  have hsum : ∑ i, finrank ℝ (Q i) ≤ r + ∑ i ∈ univ.erase i₀, 2 * r := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i₀)]
    refine Nat.add_le_add ?_ (Finset.sum_le_sum fun i hi => ?_)
    · have h0 : Q i₀ = colSpan (w i₀ • G i₀) := ite_eq_left rfl
      rw [h0]
      exact finrank_colSpan_le _
    · have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      have h0 : Q i = colSpan (w i • U i) ⊔ colSpan (w i • G i) := ite_eq_right hne
      rw [h0]
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have h1 := finrank_colSpan_le (w i • U i)
      have h2 := finrank_colSpan_le (w i • G i)
      omega
  have hcard : (univ.erase i₀).card = s - 1 := by simp
  rw [Finset.sum_const, hcard, smul_eq_mul] at hsum
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  calc finrank ℝ (augSpace U₀ w U G) ≤ finrank ℝ ↥(colSpan U₀ ⊔ univ.sup Q) :=
        Submodule.finrank_mono hle
    _ ≤ finrank ℝ (colSpan U₀) + finrank ℝ ↥(univ.sup Q) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ r + (r + (s' + 1 - 1) * (2 * r)) :=
        Nat.add_le_add (finrank_colSpan_le _) ((finrank_finset_sup_le _ _).trans hsum)
    _ = 2 * r * (s' + 1) := by simp only [Nat.add_sub_cancel]; ring

lemma norm_proj_mul_proj_le {p q : ℕ} {Uh : Matrix (Fin n) (Fin p) ℝ}
    {Vh : Matrix (Fin m) (Fin q) ℝ} (hU : Uhᵀ * Uh = 1) (hV : Vhᵀ * Vh = 1)
    (A : Matrix (Fin n) (Fin m) ℝ) : ‖Uh * Uhᵀ * (A * (Vh * Vhᵀ))‖ ≤ ‖A‖ := by
  have h1 := (isOrthProj_leftProj (n := Fin m) hU).norm_le (A * (Vh * Vhᵀ))
  have h2 := (isOrthProj_rightProj (m := Fin n) hV).norm_le A
  rw [leftProj_apply] at h1
  rw [rightProj_apply'] at h2
  exact h1.trans h2

namespace IsAugmentedUpdate

variable {Yk Ynew : LowRank n m r} {Ys : Fin s → LowRank n m r}
  {Fs : Fin s → Matrix (Fin n) (Fin m) ℝ} {h : ℝ} {w : Fin s → ℝ}
  {Yhat : Matrix (Fin n) (Fin m) ℝ}

/-- `Ŷ = Y_k + h Û Ûᵀ (∑ⱼ wⱼ Fⱼ) V̂ V̂ᵀ` gives `‖Ŷ - Y_k‖ ≤ h ∑ⱼ |wⱼ| ‖Fⱼ‖`. -/
theorem norm_hat_sub_le (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hh : 0 ≤ h) :
    ‖Yhat - Yk.mat‖ ≤ h * ∑ j, |w j| * ‖Fs j‖ := by
  obtain ⟨p, q, Uh, Vh, hU, hV, hY, -⟩ := hup
  have hUo := hU.orthonormal
  have hVo := hV.orthonormal
  have hcapU : Uh * Uhᵀ * Yk.U = Yk.U := capture_of_colSpan_le hUo (by
    rw [hU.colSpan_eq]; exact le_sup_left)
  have hcapV : Vh * Vhᵀ * Yk.V = Yk.V := capture_of_colSpan_le hVo (by
    rw [hV.colSpan_eq]; exact le_sup_left)
  have hcapV' : Yk.Vᵀ * (Vh * Vhᵀ) = Yk.Vᵀ := by
    have := congrArg Matrix.transpose hcapV
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  set G := ∑ j, w j • Fs j with hG
  have hfix : Uh * Uhᵀ * (Yk.mat * (Vh * Vhᵀ)) = Yk.mat := by
    simp only [LowRank.mat]
    rw [Matrix.mul_assoc (Yk.U * Yk.S), hcapV', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcapU]
  have hYhat : Yhat = Yk.mat + h • (Uh * Uhᵀ * (G * (Vh * Vhᵀ))) := by
    have : Uh * (Uhᵀ * (Yk.mat + h • G) * Vh) * Vhᵀ =
        Uh * Uhᵀ * ((Yk.mat + h • G) * (Vh * Vhᵀ)) := by
      simp only [Matrix.mul_assoc]
    rw [hY, this, Matrix.add_mul, Matrix.mul_add, hfix, Matrix.smul_mul, Matrix.mul_smul]
  have hnormG : ‖G‖ ≤ ∑ j, |w j| * ‖Fs j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  rw [hYhat, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left ((norm_proj_mul_proj_le hUo hVo G).trans hnormG) hh

/-- The rank of `Ŷ` is at most `min {n, m, 2 r s}`. -/
theorem rank_hat_le (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hs : 0 < s)
    (h₁ : Ys ⟨0, hs⟩ = Yk) : Yhat.rank ≤ min n (min m (2 * r * s)) := by
  obtain ⟨p, q, Uh, Vh, hU, hV, hY, -⟩ := hup
  have hp : p ≤ 2 * r * s := by
    have h1 : finrank ℝ (colSpan Uh) = p := by
      rw [finrank_colSpan, rank_eq_card_of_transpose_mul_eq_one hU.orthonormal, Fintype.card_fin]
    rw [← h1, hU.colSpan_eq]
    exact finrank_augSpace_le hs _ _ _ _ (by simp only [h₁])
  have hrankp : Yhat.rank ≤ p := by
    rw [hY, Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Uh.rank_le_card_width)
  have hn : Yhat.rank ≤ n := by simpa using Yhat.rank_le_card_height
  have hm : Yhat.rank ≤ m := by simpa using Yhat.rank_le_card_width
  omega

/-- The truncation error of one update, sharper form: `‖Ŷ - 𝓡(Ŷ)‖ ≤ ‖Ŷ - Y_k‖`. -/
theorem norm_hat_sub_new_le (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hh : 0 ≤ h) :
    ‖Yhat - Ynew.mat‖ ≤ h * ∑ j, |w j| * ‖Fs j‖ := by
  have hbest : IsBestLowRankApprox r Yhat Ynew.mat := by
    obtain ⟨p, q, Uh, Vh, -, -, -, hb⟩ := hup
    exact hb
  exact (hbest.2 _ Yk.rank_mat_le).trans (hup.norm_hat_sub_le hh)

/-- `Ynew` moves by at most twice the augmentation: `‖𝓡(Ŷ) - Y_k‖ ≤ 2 h ∑ⱼ |wⱼ| ‖Fⱼ‖`. -/
theorem norm_new_sub_le (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hh : 0 ≤ h) :
    ‖Ynew.mat - Yk.mat‖ ≤ 2 * h * ∑ j, |w j| * ‖Fs j‖ := by
  have h1 := hup.norm_hat_sub_le hh
  have h2 := hup.norm_hat_sub_new_le hh
  have h3 : ‖Ynew.mat - Yk.mat‖ ≤ ‖Yhat - Ynew.mat‖ + ‖Yhat - Yk.mat‖ := by
    have := norm_sub_le (Yhat - Yk.mat) (Yhat - Ynew.mat)
    rw [show Yhat - Yk.mat - (Yhat - Ynew.mat) = Ynew.mat - Yk.mat by abel] at this
    linarith
  linarith

/-- `‖Ŷ - 𝓡(Ŷ)‖ ≤ h (∑ⱼ |wⱼ|) B` as soon as `B` bounds `‖Fⱼ‖` for `wⱼ ≠ 0`. -/
theorem norm_hat_sub_new_le_mul (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hh : 0 ≤ h)
    {B : ℝ} (hB : ∀ j, w j ≠ 0 → ‖Fs j‖ ≤ B) :
    ‖Yhat - Ynew.mat‖ ≤ h * ((∑ j, |w j|) * B) := by
  have hsum : ∑ j, |w j| * ‖Fs j‖ ≤ (∑ j, |w j|) * B := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : w j = 0
    · simp [hj]
    · exact mul_le_mul_of_nonneg_left (hB j hj) (abs_nonneg _)
  exact (hup.norm_hat_sub_new_le hh).trans (mul_le_mul_of_nonneg_left hsum hh)

/-- The truncation error of one update with the paper's constant:
`‖Ŷ - 𝓡(Ŷ)‖ ≤ h √(min {n, m, 2 r s} - r) (∑ⱼ |wⱼ|) B` as soon as `B` bounds `‖Fⱼ‖` for `wⱼ ≠ 0`. -/
theorem norm_hat_sub_new_le_sqrt (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew) (hh : 0 ≤ h)
    (hs : 0 < s) (h₁ : Ys ⟨0, hs⟩ = Yk) {B : ℝ} (hB : ∀ j, w j ≠ 0 → ‖Fs j‖ ≤ B) :
    ‖Yhat - Ynew.mat‖ ≤
      h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * (∑ j, |w j|) * B) := by
  have hbest : IsBestLowRankApprox r Yhat Ynew.mat := by
    obtain ⟨p, q, Uh, Vh, -, -, -, hb⟩ := hup
    exact hb
  have hrank := hup.rank_hat_le hs h₁
  by_cases hmin : min n (min m (2 * r * s)) ≤ r
  · have h0 : ‖Yhat - Ynew.mat‖ ≤ 0 := by
      simpa using hbest.2 Yhat (hrank.trans hmin)
    have : min n (min m (2 * r * s)) - r = 0 := by omega
    simp only [this, Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero]
    exact h0
  · have hnn : 0 ≤ (∑ j, |w j|) * B := by
      rw [Finset.sum_mul]
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hj : w j = 0
      · simp [hj]
      · exact mul_nonneg (abs_nonneg _) ((norm_nonneg _).trans (hB j hj))
    have hone : 1 ≤ √((min n (min m (2 * r * s)) - r : ℕ) : ℝ) := by
      rw [Real.one_le_sqrt]
      have : 1 ≤ min n (min m (2 * r * s)) - r := by omega
      exact_mod_cast this
    calc ‖Yhat - Ynew.mat‖ ≤ h * ((∑ j, |w j|) * B) := hup.norm_hat_sub_new_le_mul hh hB
      _ ≤ _ := by
          rw [mul_assoc (√_)]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnn hone) hh

end IsAugmentedUpdate

/-! ### The constants of Lemmas 1 and 2 -/

namespace ExplicitRK

variable (tab : ExplicitRK s) (L h₀ : ℝ)

/-- The constants `K_{i0}` of Lemma 1. -/
noncomputable def K₀ (i : Fin s) : ℝ :=
  2 * L * ∑ j : {j : Fin s // j < i}, |tab.a i j| * (1 + K₀ j * h₀)
termination_by i
decreasing_by exact j.2

/-- The constants `K_{il}` of Lemma 1, written with one formula for all `l` (`K_{il} = 0` unless
`l < i`, see `K_eq_zero`). -/
noncomputable def K (i l : Fin s) : ℝ :=
  2 * |tab.a i l| + 2 * L * h₀ * ∑ j : {j : Fin s // j < i}, |tab.a i j| * K j l
termination_by i
decreasing_by exact j.2

/-- The constant `K̃₀` of Lemma 2. -/
noncomputable def Kt₀ : ℝ := 2 * L * ∑ i, |tab.b i| * (1 + tab.K₀ L h₀ i * h₀)

/-- The constants `K̃_l` of Lemma 2. -/
noncomputable def Kt (l : Fin s) : ℝ := 2 * |tab.b l| + 2 * L * h₀ * ∑ i, |tab.b i| * tab.K L h₀ i l

/-- The constant `C_b = ∑ᵢ |bᵢ|`. -/
def Cb : ℝ := ∑ i, |tab.b i|

/-- The analogue `∑ⱼ |a_{ij}|` of `C_b` for the stage `i`. -/
def Ca (i : Fin s) : ℝ := ∑ j, |tab.a i j|

lemma sum_subtype_lt (i : Fin s) (f : Fin s → ℝ) :
    ∑ j : {j : Fin s // j < i}, |tab.a i j| * f j = ∑ j, |tab.a i j| * f j := by
  rw [← Finset.sum_subtype (univ.filter (· < i)) (by simp) fun j => |tab.a i j| * f j]
  refine Finset.sum_filter_of_ne fun j _ hne => ?_
  by_contra hlt
  exact hne (by simp [tab.a_eq_zero i j (not_lt.mp hlt)])

lemma K₀_eq (i : Fin s) :
    tab.K₀ L h₀ i = 2 * L * ∑ j, |tab.a i j| * (1 + tab.K₀ L h₀ j * h₀) := by
  rw [K₀, sum_subtype_lt tab i fun j => 1 + tab.K₀ L h₀ j * h₀]

lemma K_eq (i l : Fin s) :
    tab.K L h₀ i l = 2 * |tab.a i l| + 2 * L * h₀ * ∑ j, |tab.a i j| * tab.K L h₀ j l := by
  rw [K, sum_subtype_lt tab i fun j => tab.K L h₀ j l]

variable {L h₀}

lemma K₀_nonneg (hL : 0 ≤ L) (hh₀ : 0 ≤ h₀) (i : Fin s) : 0 ≤ tab.K₀ L h₀ i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [K₀]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) ?_)
    have := ih j j.2
    positivity

lemma K_nonneg (hL : 0 ≤ L) (hh₀ : 0 ≤ h₀) (i l : Fin s) : 0 ≤ tab.K L h₀ i l := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [K]
    refine add_nonneg (by positivity) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (ih j j.2)))

/-- `K_{il} = 0` unless `l < i`, so that sums over all `l` are the sums `∑_{l < i}` of Lemma 1. -/
lemma K_eq_zero {i l : Fin s} (hil : i ≤ l) : tab.K L h₀ i l = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [K]
    have h0 : ∑ j : {j : Fin s // j < i}, |tab.a i j| * tab.K L h₀ j l = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [ih j j.2 (j.2.le.trans hil), mul_zero]
    simp [h0, tab.a_eq_zero i l hil]

lemma Kt₀_nonneg (hL : 0 ≤ L) (hh₀ : 0 ≤ h₀) : 0 ≤ tab.Kt₀ L h₀ := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) ?_)
  have := tab.K₀_nonneg hL hh₀ j
  positivity

lemma Kt_nonneg (hL : 0 ≤ L) (hh₀ : 0 ≤ h₀) (l : Fin s) : 0 ≤ tab.Kt L h₀ l := by
  refine add_nonneg (by positivity) (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (tab.K_nonneg hL hh₀ j l)))

/-- If `K̃₀ = 0` (and `L > 0`), then all weights vanish, so all `K̃_l` vanish. -/
lemma Kt_eq_zero_of_Kt₀_eq_zero (hL : 0 < L) (hh₀ : 0 ≤ h₀) (h0 : tab.Kt₀ L h₀ = 0)
    (l : Fin s) : tab.Kt L h₀ l = 0 := by
  have hsum : ∑ i, |tab.b i| * (1 + tab.K₀ L h₀ i * h₀) = 0 := by
    have := mul_eq_zero.mp h0
    rcases this with h | h
    · exfalso; linarith
    · exact h
  have hpos : ∀ i, 0 < 1 + tab.K₀ L h₀ i * h₀ := fun i => by
    have := tab.K₀_nonneg hL.le hh₀ i
    positivity
  have hb : ∀ i, tab.b i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (abs_nonneg (tab.b i)) (hpos i).le).mp hsum i (mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact abs_eq_zero.mp h
    · exact absurd h (hpos i).ne'
  simp [Kt, hb]

end ExplicitRK

/-- The common computation of Lemma 1 and Lemma 2. -/
lemma weighted_core {w K₀' f y φ : Fin s → ℝ} {K' : Fin s → Fin s → ℝ} {e d h h₀ L : ℝ}
    (hL : 0 ≤ L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (he : 0 ≤ e) (hK₀ : ∀ j, 0 ≤ K₀' j)
    (hK' : ∀ j l, 0 ≤ K' j l) (hf : ∀ l, 0 ≤ f l)
    (hy : ∀ j, w j ≠ 0 → y j ≤ (1 + K₀' j * h) * e + h * ∑ l, K' j l * f l)
    (hφ : ∀ j, φ j ≤ L * y j + f j) (hd : d ≤ e + 2 * h * ∑ j, |w j| * φ j) :
    d ≤ (1 + (2 * L * ∑ j, |w j| * (1 + K₀' j * h₀)) * h) * e +
      h * ∑ l, (2 * |w l| + 2 * L * h₀ * ∑ j, |w j| * K' j l) * f l := by
  set S₁ := ∑ j, |w j| * (1 + K₀' j * h₀) with hS₁
  set S₂ := ∑ j, |w j| * ∑ l, K' j l * f l with hS₂
  set S₃ := ∑ j, |w j| * f j with hS₃
  have key : ∑ j, |w j| * φ j ≤ L * e * S₁ + L * h₀ * S₂ + S₃ := by
    have hrhs : L * e * S₁ + L * h₀ * S₂ + S₃ =
        ∑ j, |w j| * (L * e * (1 + K₀' j * h₀) + L * h₀ * ∑ l, K' j l * f l + f j) := by
      have e1 : L * e * S₁ = ∑ j, L * e * (|w j| * (1 + K₀' j * h₀)) := Finset.mul_sum _ _ _
      have e2 : L * h₀ * S₂ = ∑ j, L * h₀ * (|w j| * ∑ l, K' j l * f l) := Finset.mul_sum _ _ _
      rw [e1, e2, hS₃, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrhs]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : w j = 0
    · simp [hj]
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hsum : 0 ≤ ∑ l, K' j l * f l :=
        Finset.sum_nonneg fun l _ => mul_nonneg (hK' j l) (hf l)
      have h1 : (1 + K₀' j * h) * e ≤ (1 + K₀' j * h₀) * e :=
        mul_le_mul_of_nonneg_right (by nlinarith [hK₀ j]) he
      have h2 : h * ∑ l, K' j l * f l ≤ h₀ * ∑ l, K' j l * f l :=
        mul_le_mul_of_nonneg_right hh₀ hsum
      have h3 : L * y j ≤ L * ((1 + K₀' j * h₀) * e + h₀ * ∑ l, K' j l * f l) :=
        mul_le_mul_of_nonneg_left (by linarith [hy j hj]) hL
      linarith [hφ j]
  have hsumf : ∑ l, (2 * |w l| + 2 * L * h₀ * ∑ j, |w j| * K' j l) * f l =
      2 * S₃ + 2 * L * h₀ * S₂ := by
    have h1 : ∑ l, (2 * L * h₀ * ∑ j, |w j| * K' j l) * f l = 2 * L * h₀ * S₂ := by
      simp only [hS₂, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    have h2 : ∑ l, 2 * |w l| * f l = 2 * S₃ := by
      rw [hS₃, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [add_mul, Finset.sum_add_distrib, h1, h2]
  calc d ≤ e + 2 * h * (L * e * S₁ + L * h₀ * S₂ + S₃) :=
        hd.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left key (by positivity)))
    _ = _ := by rw [hsumf]; ring

/-! ### Lemmas 1 and 2, Proposition 2 -/

section Apriori

variable {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {tab : ExplicitRK s}
  {h t L h₀ : ℝ}

lemma norm_F_le {t' : ℝ} (hLip : ∀ Z₁ Z₂, ‖F t' Z₁ - F t' Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    (Z Z₀ : Matrix (Fin n) (Fin m) ℝ) : ‖F t' Z‖ ≤ L * ‖Z - Z₀‖ + ‖F t' Z₀‖ := by
  have := norm_add_le (F t' Z - F t' Z₀) (F t' Z₀)
  rw [sub_add_cancel] at this
  linarith [hLip Z Z₀]

lemma norm_sub_le_of_step {Y Y' Z₀ : Matrix (Fin n) (Fin m) ℝ} {x : ℝ} (hx : ‖Y' - Y‖ ≤ x) :
    ‖Y' - Z₀‖ ≤ ‖Y - Z₀‖ + x := by
  have := norm_add_le (Y' - Y) (Y - Z₀)
  rw [sub_add_sub_cancel] at this
  linarith

/-- **Lemma 1** (arXiv 2502.07040): the stages of an RK-BUG step satisfy
`‖Y_{ki} - Z₀‖ ≤ (1 + K_{i0} h) ‖Y_k - Z₀‖ + h ∑_{l < i} K_{il} ‖F(t_{kl}, Z₀)‖`, with the paper's
constants (independent of `h` and `r`). The paper takes `Z₀ = Y₀`; here `Z₀` is arbitrary. -/
theorem IsRKBUGStep.stage_bound {Yk Ynext : LowRank n m r} {Ys : Fin s → LowRank n m r}
    {Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : Matrix (Fin n) (Fin m) ℝ}
    (step : IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext) (hL : 0 ≤ L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hLip : ∀ i Z₁ Z₂, ‖F (t + tab.c i * h) Z₁ - F (t + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) (i : Fin s) :
    ‖(Ys i).mat - Z₀‖ ≤ (1 + tab.K₀ L h₀ i * h) * ‖Yk.mat - Z₀‖ +
      h * ∑ l, tab.K L h₀ i l * ‖F (t + tab.c l * h) Z₀‖ := by
  have hh₀' : 0 ≤ h₀ := hh.trans hh₀
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : (i : ℕ) = 0
    · rw [step.first i hi]
      have h1 : 0 ≤ tab.K₀ L h₀ i * h * ‖Yk.mat - Z₀‖ :=
        mul_nonneg (mul_nonneg (tab.K₀_nonneg hL hh₀' i) hh) (norm_nonneg _)
      have h2 : 0 ≤ h * ∑ l, tab.K L h₀ i l * ‖F (t + tab.c l * h) Z₀‖ := mul_nonneg hh
        (Finset.sum_nonneg fun l _ => mul_nonneg (tab.K_nonneg hL hh₀' i l) (norm_nonneg _))
      nlinarith
    · have hnew := (step.stage i hi).norm_new_sub_le hh
      have := weighted_core (w := tab.a i) (K₀' := tab.K₀ L h₀) (K' := tab.K L h₀)
        (f := fun l => ‖F (t + tab.c l * h) Z₀‖) (y := fun j => ‖(Ys j).mat - Z₀‖)
        (φ := fun j => ‖F (t + tab.c j * h) (Ys j).mat‖) hL hh hh₀ (norm_nonneg (Yk.mat - Z₀))
        (tab.K₀_nonneg hL hh₀') (tab.K_nonneg hL hh₀') (fun _ => norm_nonneg _)
        (fun j hj => ih j (lt_of_not_ge fun hle => hj (tab.a_eq_zero i j hle)))
        (fun j => norm_F_le (hLip j) _ _) (norm_sub_le_of_step hnew)
      rw [tab.K₀_eq]
      simp_rw [tab.K_eq L h₀ i]
      exact this

/-- **Lemma 2** (arXiv 2502.07040): the result of an RK-BUG step satisfies
`‖Y_{k+1} - Z₀‖ ≤ (1 + K̃₀ h) ‖Y_k - Z₀‖ + h ∑ₗ K̃_l ‖F(t_{kl}, Z₀)‖`, with the paper's constants.
The paper takes `Z₀ = Y₀`; here `Z₀` is arbitrary. -/
theorem IsRKBUGStep.final_bound {Yk Ynext : LowRank n m r} {Ys : Fin s → LowRank n m r}
    {Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : Matrix (Fin n) (Fin m) ℝ}
    (step : IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext) (hL : 0 ≤ L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hLip : ∀ i Z₁ Z₂, ‖F (t + tab.c i * h) Z₁ - F (t + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) :
    ‖Ynext.mat - Z₀‖ ≤ (1 + tab.Kt₀ L h₀ * h) * ‖Yk.mat - Z₀‖ +
      h * ∑ l, tab.Kt L h₀ l * ‖F (t + tab.c l * h) Z₀‖ := by
  have hh₀' : 0 ≤ h₀ := hh.trans hh₀
  exact weighted_core (w := tab.b) (K₀' := tab.K₀ L h₀) (K' := tab.K L h₀)
    (f := fun l => ‖F (t + tab.c l * h) Z₀‖) (y := fun j => ‖(Ys j).mat - Z₀‖)
    (φ := fun j => ‖F (t + tab.c j * h) (Ys j).mat‖) hL hh hh₀ (norm_nonneg (Yk.mat - Z₀))
    (tab.K₀_nonneg hL hh₀') (tab.K_nonneg hL hh₀') (fun _ => norm_nonneg _)
    (fun j _ => step.stage_bound hL hh hh₀ hLip Z₀ j)
    (fun j => norm_F_le (hLip j) _ _) (norm_sub_le_of_step (step.final.norm_new_sub_le hh))

/-- **Proposition 2** (arXiv 2502.07040): for `k ≤ N`,
`‖Y_k - Y₀‖ ≤ (e^{k h K̃₀} - 1) / K̃₀ · G` for every `G` bounding
`∑ᵢ K̃ᵢ ‖F(t_{li}, Y₀)‖`, `l < k` (the paper takes the maximum). If `K̃₀ = 0`, which for `L > 0`
means that all `bᵢ` vanish, then `Y_k = Y₀`, in agreement with Lean's `x / 0 = 0`. -/
theorem IsRKBUGSolution.norm_sub_le {N : ℕ} {Y : ℕ → LowRank n m r}
    {Ys : ℕ → Fin s → LowRank n m r} {Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ}
    {Yh : ℕ → Matrix (Fin n) (Fin m) ℝ} (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh)
    (hL : 0 < L) (hh : 0 ≤ h) (hh₀ : h ≤ h₀)
    (hLip : ∀ k < N, ∀ i Z₁ Z₂, ‖F ((k : ℝ) * h + tab.c i * h) Z₁ -
      F ((k : ℝ) * h + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖)
    {k : ℕ} (hk : k ≤ N) {G : ℝ}
    (hG : ∀ l < k, ∑ i, tab.Kt L h₀ i * ‖F ((l : ℝ) * h + tab.c i * h) (Y 0).mat‖ ≤ G) :
    ‖(Y k).mat - (Y 0).mat‖ ≤ (Real.exp ((k : ℝ) * h * tab.Kt₀ L h₀) - 1) / tab.Kt₀ L h₀ * G := by
  have hh₀' : 0 ≤ h₀ := hh.trans hh₀
  set K := tab.Kt₀ L h₀ with hKdef
  have hstep : ∀ l, l < N → ‖(Y (l + 1)).mat - (Y 0).mat‖ ≤ (1 + K * h) * ‖(Y l).mat - (Y 0).mat‖ +
      h * ∑ i, tab.Kt L h₀ i * ‖F ((l : ℝ) * h + tab.c i * h) (Y 0).mat‖ := fun l hl =>
    (hsol l hl).final_bound hL.le hh hh₀ (hLip l hl) _
  rcases (tab.Kt₀_nonneg hL.le hh₀').eq_or_lt with hK | hK
  · -- `K̃₀ = 0`: the solution does not move
    have hK' : K = 0 := hK.symm
    have hzero : ∀ j, j ≤ N → ‖(Y j).mat - (Y 0).mat‖ ≤ 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        intro hj
        have h1 := hstep j (by omega)
        simp only [hK', tab.Kt_eq_zero_of_Kt₀_eq_zero hL hh₀' hK.symm, zero_mul,
          Finset.sum_const_zero, mul_zero, add_zero, one_mul] at h1
        exact h1.trans (ih (by omega))
    rw [hK']
    simpa using hzero k hk
  · have hind : ∀ j, j ≤ k → ‖(Y j).mat - (Y 0).mat‖ ≤ ((1 + K * h) ^ j - 1) / K * G := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        intro hj
        have h1 := hstep j (by omega)
        have h2 := ih (by omega)
        have h3 := mul_le_mul_of_nonneg_left (hG j (by omega)) hh
        have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 + K * h)
        have heq : (1 + K * h) * (((1 + K * h) ^ j - 1) / K * G) + h * G =
            ((1 + K * h) ^ (j + 1) - 1) / K * G := by
          have hKne : K ≠ 0 := hK.ne'
          field_simp
          ring
        linarith
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    have hG0 : 0 ≤ G := (Finset.sum_nonneg fun i _ =>
      mul_nonneg (tab.Kt_nonneg hL.le hh₀' i) (norm_nonneg _)).trans (hG 0 hkpos)
    refine (hind k le_rfl).trans (mul_le_mul_of_nonneg_right ?_ hG0)
    refine div_le_div_of_nonneg_right (sub_le_sub_right ?_ _) hK.le
    have h1 : 1 + K * h ≤ Real.exp (K * h) := by linarith [Real.add_one_le_exp (K * h)]
    calc (1 + K * h) ^ k ≤ Real.exp (K * h) ^ k := pow_le_pow_left₀ (by positivity) h1 k
      _ = Real.exp ((k : ℝ) * h * K) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

end Apriori

/-! ### The neighbourhood `𝓥_r`, the bound `B`, and Proposition 4 -/

/-- **Assumption 1** of arXiv 2502.07040: `F` is continuous in time and uniformly `L`-Lipschitz in
`Z` on `[0, T]`, with `L > 0`. -/
structure Assumption1 (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (L T : ℝ) : Prop where
  pos : 0 < L
  cont : ∀ Z, ContinuousOn (fun t => F t Z) (Icc 0 T)
  lip : ∀ t ∈ Icc 0 T, ∀ Z₁ Z₂, ‖F t Z₁ - F t Z₂‖ ≤ L * ‖Z₁ - Z₂‖

/-- The set `𝓥_r` of eq. (19), with `R` for `max {R₁, R₂}`. The rank constraint reads `rank ≤ r`:
this is the closure of the manifold `𝓜_r`, it is what makes `𝓥_r` compact as the paper claims,
and the iterates need not have rank exactly `r`. -/
def nbhdV (Z₀ : Matrix (Fin n) (Fin m) ℝ) (R : ℝ) (r : ℕ) : Set (Matrix (Fin n) (Fin m) ℝ) :=
  {Z | Z.rank ≤ r ∧ ‖Z - Z₀‖ ≤ R}

/-- `sup_{t ∈ [0, T]} ‖F(t, Z₀)‖`. -/
noncomputable def supF (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (T : ℝ)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  sSup ((fun t => ‖F t Z₀‖) '' Icc 0 T)

/-- The radius `R₁ = ∫₀ᵀ e^{L (T - t)} ‖F(t, Y₀)‖ dt` below eq. (19). -/
noncomputable def R₁ (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (L T : ℝ)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Real.exp (L * (T - t)) * ‖F t Z₀‖

/-- The radius `R₂` below eq. (19). -/
noncomputable def R₂ (tab : ExplicitRK s)
    (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (L T h₀ : ℝ)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (⨆ i, (1 + tab.K₀ L h₀ i * h₀) *
      ((Real.exp (T * tab.Kt₀ L h₀) - 1) / tab.Kt₀ L h₀ * ∑ j, tab.Kt L h₀ j) +
      h₀ * ∑ j, tab.K L h₀ i j) * supF F T Z₀

/-- The bound `B = sup_{t ∈ [0, T]} sup_{Z ∈ 𝓥_r} ‖F(t, Z)‖` of eq. (20). -/
noncomputable def boundB (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (T : ℝ)
    (Z₀ : Matrix (Fin n) (Fin m) ℝ) (R : ℝ) (r : ℕ) : ℝ :=
  sSup ((fun p : ℝ × Matrix (Fin n) (Fin m) ℝ => ‖F p.1 p.2‖) '' (Icc 0 T ×ˢ nbhdV Z₀ R r))

section Main

variable {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {L T h₀ h : ℝ}
  {tab : ExplicitRK s} {N : ℕ} {Y : ℕ → LowRank n m r} {Ys : ℕ → Fin s → LowRank n m r}
  {Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : ℕ → Matrix (Fin n) (Fin m) ℝ}

lemma bddAbove_supF (hA : Assumption1 F L T) (Z₀ : Matrix (Fin n) (Fin m) ℝ) :
    BddAbove ((fun t => ‖F t Z₀‖) '' Icc 0 T) :=
  (isCompact_Icc.image_of_continuousOn (hA.cont Z₀).norm).bddAbove

lemma norm_le_supF (hA : Assumption1 F L T) (Z₀ : Matrix (Fin n) (Fin m) ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) : ‖F t Z₀‖ ≤ supF F T Z₀ :=
  le_csSup (bddAbove_supF hA Z₀) ⟨t, ht, rfl⟩

lemma supF_nonneg (Z₀ : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ supF F T Z₀ :=
  Real.sSup_nonneg (by rintro _ ⟨t, -, rfl⟩; exact norm_nonneg _)

/-- `B` is finite: by compactness of `[0, T]` and the Lipschitz bound. This is the only place where
continuity in time enters. -/
lemma bddAbove_boundB (hA : Assumption1 F L T) (Z₀ : Matrix (Fin n) (Fin m) ℝ) (R : ℝ) (r : ℕ) :
    BddAbove ((fun p : ℝ × Matrix (Fin n) (Fin m) ℝ => ‖F p.1 p.2‖) ''
      (Icc 0 T ×ˢ nbhdV Z₀ R r)) := by
  refine ⟨supF F T Z₀ + L * R, ?_⟩
  rintro _ ⟨⟨t, Z⟩, ⟨ht, hZ⟩, rfl⟩
  have h1 := norm_F_le (hA.lip t ht) Z Z₀
  have h2 := mul_le_mul_of_nonneg_left hZ.2 hA.pos.le
  have h3 := norm_le_supF hA Z₀ ht
  simp only
  linarith

lemma norm_le_boundB (hA : Assumption1 F L T) {Z₀ : Matrix (Fin n) (Fin m) ℝ} {R : ℝ} {t : ℝ}
    {Z : Matrix (Fin n) (Fin m) ℝ} (ht : t ∈ Icc 0 T) (hZ : Z ∈ nbhdV Z₀ R r) :
    ‖F t Z‖ ≤ boundB F T Z₀ R r :=
  le_csSup (bddAbove_boundB hA Z₀ R r) ⟨(t, Z), ⟨ht, hZ⟩, rfl⟩

lemma time_mem (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1) (hh : 0 ≤ h) (hN : (N : ℝ) * h ≤ T) {k : ℕ}
    (hk : k < N) (i : Fin s) : (k : ℝ) * h + tab.c i * h ∈ Icc 0 T := by
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have h1 := mul_le_mul_of_nonneg_right hk' hh
  have h2 := mul_nonneg (hc i).1 hh
  have h3 := mul_le_mul_of_nonneg_right (hc i).2 hh
  constructor
  · positivity
  · linarith

/-- The content of the definition of `R₂` (paper, before eq. (19)): every stage of every step lies
in `𝓥_r`, with radius `R₂`. -/
theorem stage_mem_nbhdV (hA : Assumption1 F L T) (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1)
    (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {k : ℕ} (hk : k < N) (i : Fin s) :
    (Ys k i).mat ∈ nbhdV (Y 0).mat (R₂ tab F L T h₀ (Y 0).mat) r := by
  refine ⟨(Ys k i).rank_mat_le, ?_⟩
  have hL := hA.pos
  have hh₀' : 0 ≤ h₀ := hh.trans hh₀
  set Z₀ := (Y 0).mat with hZ₀
  set σ := supF F T Z₀ with hσ
  have hσ0 : 0 ≤ σ := supF_nonneg _
  set K := tab.Kt₀ L h₀ with hK
  have hK0 : 0 ≤ K := tab.Kt₀_nonneg hL.le hh₀'
  have hLip : ∀ k < N, ∀ i Z₁ Z₂, ‖F ((k : ℝ) * h + tab.c i * h) Z₁ -
      F ((k : ℝ) * h + tab.c i * h) Z₂‖ ≤ L * ‖Z₁ - Z₂‖ := fun k hk i =>
    hA.lip _ (time_mem hc hh hN hk i)
  have hf : ∀ {l : ℕ}, l < N → ∀ j, ‖F ((l : ℝ) * h + tab.c j * h) Z₀‖ ≤ σ := fun hl j =>
    norm_le_supF hA Z₀ (time_mem hc hh hN hl j)
  set G := (∑ j, tab.Kt L h₀ j) * σ with hG
  have hG0 : 0 ≤ G := mul_nonneg
    (Finset.sum_nonneg fun j _ => tab.Kt_nonneg hL.le hh₀' j) hσ0
  have hE : ‖(Y k).mat - Z₀‖ ≤ (Real.exp (T * K) - 1) / K * G := by
    have h1 := hsol.norm_sub_le hL hh hh₀ hLip hk.le (G := G) fun l hl => by
      rw [hG, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf (hl.trans hk) j)
        (tab.Kt_nonneg hL.le hh₀' j)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hG0)
    refine div_le_div_of_nonneg_right (sub_le_sub_right (Real.exp_le_exp.mpr ?_) _) hK0
    refine mul_le_mul_of_nonneg_right ?_ hK0
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    exact (mul_le_mul_of_nonneg_right hk' hh).trans hN
  have hstage := (hsol k hk).stage_bound hL.le hh hh₀ (hLip k hk) Z₀ i
  have hK₀i := tab.K₀_nonneg hL.le hh₀' i
  have h1 : (1 + tab.K₀ L h₀ i * h) * ‖(Y k).mat - Z₀‖ ≤
      (1 + tab.K₀ L h₀ i * h₀) * ((Real.exp (T * K) - 1) / K * G) := by
    refine mul_le_mul (by nlinarith) hE (norm_nonneg _) (by positivity)
  have hsumK : 0 ≤ ∑ j, tab.K L h₀ i j := Finset.sum_nonneg fun j _ => tab.K_nonneg hL.le hh₀' i j
  have h2 : h * ∑ l, tab.K L h₀ i l * ‖F ((k : ℝ) * h + tab.c l * h) Z₀‖ ≤
      h₀ * ((∑ j, tab.K L h₀ i j) * σ) := by
    refine mul_le_mul hh₀ ?_ (Finset.sum_nonneg fun j _ =>
      mul_nonneg (tab.K_nonneg hL.le hh₀' i j) (norm_nonneg _)) hh₀'
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf hk j)
      (tab.K_nonneg hL.le hh₀' i j)
  have h3 : (1 + tab.K₀ L h₀ i * h₀) * ((Real.exp (T * K) - 1) / K * ∑ j, tab.Kt L h₀ j) +
      h₀ * ∑ j, tab.K L h₀ i j ≤
      ⨆ i, (1 + tab.K₀ L h₀ i * h₀) * ((Real.exp (T * K) - 1) / K * ∑ j, tab.Kt L h₀ j) +
      h₀ * ∑ j, tab.K L h₀ i j :=
    le_ciSup (f := fun i => (1 + tab.K₀ L h₀ i * h₀) *
      ((Real.exp (T * K) - 1) / K * ∑ j, tab.Kt L h₀ j) + h₀ * ∑ j, tab.K L h₀ i j)
      (Set.finite_range _).bddAbove i
  calc ‖(Ys k i).mat - Z₀‖
      ≤ (1 + tab.K₀ L h₀ i * h₀) * ((Real.exp (T * K) - 1) / K * G) +
          h₀ * ((∑ j, tab.K L h₀ i j) * σ) := by linarith
    _ = ((1 + tab.K₀ L h₀ i * h₀) * ((Real.exp (T * K) - 1) / K * ∑ j, tab.Kt L h₀ j) +
          h₀ * ∑ j, tab.K L h₀ i j) * σ := by rw [hG]; ring
    _ ≤ R₂ tab F L T h₀ Z₀ := mul_le_mul_of_nonneg_right h3 hσ0

/-- The stage derivatives are bounded by `B` (used in eq. (29)); `R` is any radius above `R₂`. -/
theorem norm_stage_F_le (hA : Assumption1 F L T) (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1)
    (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {R : ℝ}
    (hR : R₂ tab F L T h₀ (Y 0).mat ≤ R) {k : ℕ} (hk : k < N) (i : Fin s) :
    ‖F ((k : ℝ) * h + tab.c i * h) (Ys k i).mat‖ ≤ boundB F T (Y 0).mat R r := by
  have hmem := stage_mem_nbhdV hA hc hh hh₀ hN hsol hk i
  exact norm_le_boundB hA (time_mem hc hh hN hk i) ⟨hmem.1, hmem.2.trans hR⟩

/-- **Proposition 4** (arXiv 2502.07040, eqs. (25)–(26)): under Assumption 1, for `0 ≤ h ≤ h₀`,
`N h ≤ T` and every `k < N`, the truncation errors of the RK-BUG integrator satisfy

* `‖Ŷ_{k+1} - 𝓡(Ŷ_{k+1})‖ ≤ h √(min {n, m, 2 r s} - r) C_b B`, and
* `‖Ŷ_{k,i} - 𝓡(Ŷ_{k,i})‖ ≤ h √(min {n, m, 2 r s} - r) (∑ⱼ |a_{ij}|) B` for the stages `i ≥ 2`,

where `B` is the supremum (20) over `𝓥_r` with radius `max {R₁, R₂}`, which does not depend on `h`.
`𝓡(Ŷ)` is any best rank-`r` approximation of `Ŷ`.

Differences from the paper. The subtraction in the root is in `ℕ`, so the root is `0` if
`r ≥ min {n, m, 2 r s}`. The paper states (26) with the same `γ̄_r` as (25) and gives the constant
only for (25), where it uses the weights `b`; for the stages the argument gives the weights
`a_{ij}`, whose sum can exceed `C_b`. See `truncation_error_gamma` for one uniform constant. The
hypothesis `0 ≤ c_i ≤ 1` keeps the stage times in `[0, T]`, where the paper's Assumption 1 lives. -/
theorem truncation_error (hs : 0 < s) (hA : Assumption1 F L T)
    (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {k : ℕ} (hk : k < N) :
    ‖Yh k - (Y (k + 1)).mat‖ ≤ h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * tab.Cb *
      boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) ∧
    ∀ i : Fin s, (i : ℕ) ≠ 0 →
      ‖Yhs k i - (Ys k i).mat‖ ≤ h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * tab.Ca i *
        boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) := by
  have hB := fun j => norm_stage_F_le hA hc hh hh₀ hN hsol
    (le_max_right (R₁ F L T (Y 0).mat) _) hk j
  have h₁ := (hsol k hk).first ⟨0, hs⟩ rfl
  exact ⟨(hsol k hk).final.norm_hat_sub_new_le_sqrt hh hs h₁ fun j _ => hB j,
    fun i hi => ((hsol k hk).stage i hi).norm_hat_sub_new_le_sqrt hh hs h₁ fun j _ => hB j⟩

end Main

/-- The constant `γ̄_r` of Proposition 4, uniform in the stages: the paper's
`√(min {n, m, 2 r s} - r) C_b B` with `C_b` replaced by `max {C_b, maxᵢ ∑ⱼ |a_{ij}|}`. -/
noncomputable def gammaBar (tab : ExplicitRK s) (n m r : ℕ) (B : ℝ) : ℝ :=
  √((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * max tab.Cb (⨆ i, tab.Ca i) * B

/-- `γ̄_r` vanishes when `r = min {n, m}`, as claimed in Proposition 4. -/
theorem gammaBar_eq_zero (tab : ExplicitRK s) (B : ℝ) (hr : min n m ≤ r) :
    gammaBar tab n m r B = 0 := by
  have : min n (min m (2 * r * s)) - r = 0 := by omega
  simp [gammaBar, this]

lemma boundB_nonneg {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {T R : ℝ}
    {Z₀ : Matrix (Fin n) (Fin m) ℝ} : 0 ≤ boundB F T Z₀ R r :=
  Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg _)

lemma Ca_le_max (tab : ExplicitRK s) (i : Fin s) : tab.Ca i ≤ max tab.Cb (⨆ i, tab.Ca i) :=
  (le_ciSup (f := tab.Ca) (Set.finite_range _).bddAbove i).trans (le_max_right _ _)

section Main2

variable {F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ} {L T h₀ h : ℝ}
  {tab : ExplicitRK s} {N : ℕ} {Y : ℕ → LowRank n m r} {Ys : ℕ → Fin s → LowRank n m r}
  {Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ} {Yh : ℕ → Matrix (Fin n) (Fin m) ℝ}

/-- **Proposition 4** (arXiv 2502.07040, eqs. (25)–(26)) with one constant: the truncation errors at
the final stage and at all stages are at most `h γ̄_r`, where `γ̄_r = gammaBar tab n m r B` does not
depend on `h` and vanishes for `r = min {n, m}` (`gammaBar_eq_zero`). Difference from the paper:
`C_b` becomes `max {C_b, maxᵢ ∑ⱼ |a_{ij}|}`, see `truncation_error`. -/
theorem truncation_error_gamma (hs : 0 < s) (hA : Assumption1 F L T)
    (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {k : ℕ} (hk : k < N) :
    ‖Yh k - (Y (k + 1)).mat‖ ≤ h * gammaBar tab n m r
      (boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) ∧
    ∀ i : Fin s, (i : ℕ) ≠ 0 → ‖Yhs k i - (Ys k i).mat‖ ≤ h * gammaBar tab n m r
      (boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) := by
  obtain ⟨h1, h2⟩ := truncation_error hs hA hc hh hh₀ hN hsol hk
  have hmono : ∀ {C : ℝ}, C ≤ max tab.Cb (⨆ i, tab.Ca i) → ∀ B : ℝ, 0 ≤ B →
      h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * C * B) ≤ h * gammaBar tab n m r B :=
    fun hC B hB => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)) hB) hh
  exact ⟨h1.trans (hmono (le_max_left _ _) _ boundB_nonneg),
    fun i hi => (h2 i hi).trans (hmono (Ca_le_max tab i) _ boundB_nonneg)⟩

/-- **Proposition 4** (arXiv 2502.07040, eqs. (25)–(26)) for the truncated SVD `truncation Ŷ r` of
the library, `Ŷ V_r V_rᵀ`, in place of a general best approximation. -/
theorem truncation_error_truncation (hs : 0 < s) (hA : Assumption1 F L T)
    (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {k : ℕ} (hk : k < N) :
    ‖Yh k - truncation (Yh k) r‖ ≤ h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * tab.Cb *
      boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) ∧
    ∀ i : Fin s, (i : ℕ) ≠ 0 →
      ‖Yhs k i - truncation (Yhs k i) r‖ ≤
        h * (√((min n (min m (2 * r * s)) - r : ℕ) : ℝ) * tab.Ca i *
          boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) := by
  obtain ⟨h1, h2⟩ := truncation_error hs hA hc hh hh₀ hN hsol hk
  exact ⟨(norm_sub_truncation_le _ (Y (k + 1)).rank_mat_le).trans h1,
    fun i hi => (norm_sub_truncation_le _ (Ys k i).rank_mat_le).trans (h2 i hi)⟩

/-- **Sharper form of Proposition 4** (arXiv 2502.07040): the factor `√(min {n, m, 2 r s} - r)` is
not needed when it is at least `1`, as `‖Ŷ - 𝓡(Ŷ)‖ ≤ ‖Ŷ - Y_k‖` by Eckart–Young. The paper bounds
each squared singular value by the sum of all of them in (29), which loses this factor; its role is
only to make the bound vanish at full rank. -/
theorem truncation_error_sharp (hA : Assumption1 F L T)
    (hc : ∀ i, 0 ≤ tab.c i ∧ tab.c i ≤ 1) (hh : 0 ≤ h) (hh₀ : h ≤ h₀) (hN : (N : ℝ) * h ≤ T)
    (hsol : IsRKBUGSolution F tab h N Y Ys Yhs Yh) {k : ℕ} (hk : k < N) :
    ‖Yh k - (Y (k + 1)).mat‖ ≤ h * (tab.Cb *
      boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) ∧
    ∀ i : Fin s, (i : ℕ) ≠ 0 → ‖Yhs k i - (Ys k i).mat‖ ≤ h * (tab.Ca i *
      boundB F T (Y 0).mat (max (R₁ F L T (Y 0).mat) (R₂ tab F L T h₀ (Y 0).mat)) r) := by
  have hB := fun j => norm_stage_F_le hA hc hh hh₀ hN hsol
    (le_max_right (R₁ F L T (Y 0).mat) _) hk j
  exact ⟨(hsol k hk).final.norm_hat_sub_new_le_mul hh fun j _ => hB j,
    fun i hi => ((hsol k hk).stage i hi).norm_hat_sub_new_le_mul hh fun j _ => hB j⟩

end Main2

/-! ### Algorithm 2 is well defined: the hypotheses can hold -/

section Existence

lemma exists_isOrthOf {d : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    ∃ (p : ℕ) (Q : Matrix (Fin d) (Fin p) ℝ), IsOrthOf Q W := by
  obtain ⟨u, hu, hmem, hW⟩ := exists_orthonormal_of_le (W := W) (V := W) le_rfl le_rfl le_rfl
  refine ⟨_, ofCols u, ⟨transpose_ofCols_mul_ofCols hu, le_antisymm ?_ hW⟩⟩
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact hmem j

lemma exists_lowRank_mat_eq (hn : r ≤ n) (hm : r ≤ m) {X : Matrix (Fin n) (Fin m) ℝ}
    (hX : X.rank ≤ r) : ∃ Y : LowRank n m r, Y.mat = X := by
  obtain ⟨U, hU, hUX⟩ := exists_orthonormal_capture X hX (by simpa using hn)
  obtain ⟨V, hV, hVX⟩ := exists_orthonormal_capture (r := r) Xᵀ
    (by rw [Matrix.rank_transpose]; exact hX) (by simpa using hm)
  have hVX' : X * (V * Vᵀ) = X := by
    have := congrArg Matrix.transpose hVX
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  refine ⟨⟨U, Uᵀ * X * V, V, hU, hV⟩, ?_⟩
  simp only [LowRank.mat]
  calc U * (Uᵀ * X * V) * Vᵀ = U * Uᵀ * (X * (V * Vᵀ)) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hVX', hUX]

lemma LowRank.le_left (Y : LowRank n m r) : r ≤ n := by
  have h := rank_eq_card_of_transpose_mul_eq_one Y.U_orth
  have h2 := Y.U.rank_le_card_height
  simp only [Fintype.card_fin] at h h2
  omega

lemma LowRank.le_right (Y : LowRank n m r) : r ≤ m := by
  have h := rank_eq_card_of_transpose_mul_eq_one Y.V_orth
  have h2 := Y.V.rank_le_card_height
  simp only [Fintype.card_fin] at h h2
  omega

lemma augSpace_congr {d : ℕ} {U₀ : Matrix (Fin d) (Fin r) ℝ} {w : Fin s → ℝ}
    {U U' G G' : Fin s → Matrix (Fin d) (Fin r) ℝ} (hU : ∀ j, w j ≠ 0 → U' j = U j)
    (hG : ∀ j, w j ≠ 0 → G' j = G j) : augSpace U₀ w U' G' = augSpace U₀ w U G := by
  have key : ∀ (A A' : Fin s → Matrix (Fin d) (Fin r) ℝ), (∀ j, w j ≠ 0 → A' j = A j) →
      ∀ j, w j • A' j = w j • A j := fun A A' hA j => by
    by_cases hj : w j = 0
    · simp [hj]
    · rw [hA j hj]
  simp only [augSpace, key U U' hU, key G G' hG]

lemma IsAugmentedUpdate.congr {Yk Ynew : LowRank n m r} {Ys Ys' : Fin s → LowRank n m r}
    {Fs Fs' : Fin s → Matrix (Fin n) (Fin m) ℝ} {h : ℝ} {w : Fin s → ℝ}
    {Yhat : Matrix (Fin n) (Fin m) ℝ} (hup : IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew)
    (hY : ∀ j, w j ≠ 0 → Ys' j = Ys j) (hF : ∀ j, w j ≠ 0 → Fs' j = Fs j) :
    IsAugmentedUpdate Yk Ys' Fs' h w Yhat Ynew := by
  obtain ⟨p, q, Uh, Vh, hU, hV, hYh, hb⟩ := hup
  have e1 : augSpace Yk.U w (fun i => (Ys' i).U) (fun i => Fs' i * (Ys' i).V) =
      augSpace Yk.U w (fun i => (Ys i).U) (fun i => Fs i * (Ys i).V) :=
    augSpace_congr (fun j hj => by simp only [hY j hj]) fun j hj => by
      simp only [hY j hj, hF j hj]
  have e2 : augSpace Yk.V w (fun i => (Ys' i).V) (fun i => (Fs' i)ᵀ * (Ys' i).U) =
      augSpace Yk.V w (fun i => (Ys i).V) (fun i => (Fs i)ᵀ * (Ys i).U) :=
    augSpace_congr (fun j hj => by simp only [hY j hj]) fun j hj => by
      simp only [hY j hj, hF j hj]
  have e3 : ∑ j, w j • Fs' j = ∑ j, w j • Fs j := Finset.sum_congr rfl fun j _ => by
    by_cases hj : w j = 0
    · simp [hj]
    · rw [hF j hj]
  refine ⟨p, q, Uh, Vh, ?_, ?_, ?_, hb⟩
  · rw [e1]; exact hU
  · rw [e2]; exact hV
  · rw [e3]; exact hYh

lemma exists_update (Yk : LowRank n m r) (Ys : Fin s → LowRank n m r)
    (Fs : Fin s → Matrix (Fin n) (Fin m) ℝ) (h : ℝ) (w : Fin s → ℝ) :
    ∃ (Yhat : Matrix (Fin n) (Fin m) ℝ) (Ynew : LowRank n m r),
      IsAugmentedUpdate Yk Ys Fs h w Yhat Ynew := by
  obtain ⟨p, Uh, hU⟩ := exists_isOrthOf
    (augSpace Yk.U w (fun i => (Ys i).U) fun i => Fs i * (Ys i).V)
  obtain ⟨q, Vh, hV⟩ := exists_isOrthOf
    (augSpace Yk.V w (fun i => (Ys i).V) fun i => (Fs i)ᵀ * (Ys i).U)
  set Yhat := Uh * (Uhᵀ * (Yk.mat + h • ∑ j, w j • Fs j) * Vh) * Vhᵀ with hYhat
  obtain ⟨Ynew, hnew⟩ := exists_lowRank_mat_eq Yk.le_left Yk.le_right
    (rank_truncation_le Yhat r)
  refine ⟨Yhat, Ynew, p, q, Uh, Vh, hU, hV, rfl, Ynew.rank_mat_le, fun Z hZ => ?_⟩
  rw [hnew]
  exact norm_sub_truncation_le Yhat hZ

variable (F : ℝ → Matrix (Fin n) (Fin m) ℝ → Matrix (Fin n) (Fin m) ℝ) (tab : ExplicitRK s)
  (h : ℝ)

lemma exists_stages (t : ℝ) (Yk : LowRank n m r) (q : ℕ) (hq : q ≤ s) :
    ∃ (Ys : Fin s → LowRank n m r) (Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ),
      (∀ i : Fin s, (i : ℕ) = 0 → Ys i = Yk) ∧
      ∀ i : Fin s, (i : ℕ) ≠ 0 → (i : ℕ) < q → IsAugmentedUpdate Yk Ys
        (fun j => F (t + tab.c j * h) (Ys j).mat) h (tab.a i) (Yhs i) (Ys i) := by
  classical
  induction q with
  | zero => exact ⟨fun _ => Yk, fun _ => 0, fun _ _ => rfl, fun i _ hi => absurd hi (by omega)⟩
  | succ q ih =>
    obtain ⟨Ys, Yhs, h1, h2⟩ := ih (by omega)
    by_cases hq0 : q = 0
    · exact ⟨Ys, Yhs, h1, fun i hi hi' => absurd hi (by omega)⟩
    let iq : Fin s := ⟨q, by omega⟩
    have hiq : (iq : ℕ) = q := rfl
    obtain ⟨Yhat, Ynew, hup⟩ := exists_update Yk Ys
      (fun j => F (t + tab.c j * h) (Ys j).mat) h (tab.a iq)
    have hupd : ∀ i : Fin s, (i : ℕ) ≤ q → ∀ j, tab.a i j ≠ 0 →
        Function.update Ys iq Ynew j = Ys j := fun i hi j hj => by
      refine Function.update_of_ne ?_ _ _
      intro hjq
      have hlt : j < i := lt_of_not_ge fun hle => hj (tab.a_eq_zero i j hle)
      rw [hjq] at hlt
      have hlt' : (iq : ℕ) < i := hlt
      omega
    refine ⟨Function.update Ys iq Ynew, Function.update Yhs iq Yhat, fun i hi => ?_,
      fun i hi hi' => ?_⟩
    · have hne : i ≠ iq := fun he => hq0 (by rw [← hiq, ← he]; exact hi)
      rw [Function.update_of_ne hne]
      exact h1 i hi
    · by_cases hie : i = iq
      · subst hie
        rw [Function.update_self, Function.update_self]
        exact hup.congr (hupd iq le_rfl) fun j hj => by simp only [hupd iq le_rfl j hj]
      · have hlt : (i : ℕ) < q := by
          have : (i : ℕ) ≠ q := fun he => hie (Fin.ext he)
          omega
        rw [Function.update_of_ne hie, Function.update_of_ne hie]
        exact (h2 i hi hlt).congr (hupd i hlt.le) fun j hj => by
          simp only [hupd i hlt.le j hj]

/-- **Algorithm 2 is well defined**: from every `Y_k`, for every `F`, tableau and step size, an
RK-BUG step exists. -/
theorem exists_rkbug_step (t : ℝ) (Yk : LowRank n m r) :
    ∃ (Ys : Fin s → LowRank n m r) (Yhs : Fin s → Matrix (Fin n) (Fin m) ℝ)
      (Yh : Matrix (Fin n) (Fin m) ℝ) (Ynext : LowRank n m r),
      IsRKBUGStep F tab h t Yk Ys Yhs Yh Ynext := by
  obtain ⟨Ys, Yhs, h1, h2⟩ := exists_stages F tab h t Yk s le_rfl
  obtain ⟨Yh, Ynext, h3⟩ := exists_update Yk Ys (fun j => F (t + tab.c j * h) (Ys j).mat) h tab.b
  exact ⟨Ys, Yhs, Yh, Ynext, ⟨h1, fun i hi => h2 i hi i.2, h3⟩⟩

/-- **Non-vacuity**: every initial value `Y₀` starts an RK-BUG solution, for every `F`, tableau and
step size, so `IsRKBUGSolution` in Proposition 4 can hold. -/
theorem exists_rkbug_solution (N : ℕ) (Y₀ : LowRank n m r) :
    ∃ (Y : ℕ → LowRank n m r) (Ys : ℕ → Fin s → LowRank n m r)
      (Yhs : ℕ → Fin s → Matrix (Fin n) (Fin m) ℝ) (Yh : ℕ → Matrix (Fin n) (Fin m) ℝ),
      Y 0 = Y₀ ∧ IsRKBUGSolution F tab h N Y Ys Yhs Yh := by
  choose Ys' Yhs' Yh' next hstep using fun (k : ℕ) (Yk : LowRank n m r) =>
    exists_rkbug_step F tab h ((k : ℝ) * h) Yk
  let Y : ℕ → LowRank n m r := fun k => Nat.rec Y₀ (fun k y => next k y) k
  exact ⟨Y, fun k => Ys' k (Y k), fun k => Yhs' k (Y k), fun k => Yh' k (Y k), rfl,
    fun k _ => hstep k (Y k)⟩

end Existence

/-- Assumption 1 holds for instance for `F(t, Z) = Z`. -/
example (T : ℝ) : Assumption1 (fun _ (Z : Matrix (Fin n) (Fin m) ℝ) => Z) 1 T :=
  ⟨one_pos, fun _ => continuousOn_const, fun _ _ _ _ => by simp⟩

/-- The tableau of the forward Euler method, for which Algorithm 2 is Algorithm 1. -/
example : ExplicitRK 1 :=
  ⟨fun _ _ => 0, fun _ => 1, fun _ => 0, fun _ _ _ => rfl⟩

/-! ### The stage bound (26) needs the weights `a`, not `C_b` -/

section Counterexample

/-- Kutta's third-order method; here `C_b = 1` but `∑ⱼ |a_{3j}| = 3`. -/
noncomputable def kutta3 : ExplicitRK 3 where
  a := !![0, 0, 0; 1 / 2, 0, 0; -1, 2, 0]
  b := ![1 / 6, 2 / 3, 1 / 6]
  c := ![0, 1 / 2, 1]
  a_eq_zero := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The swap matrix `[[0, 1], [1, 0]]`. -/
def swapA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The first unit vector, as a `2 × 1` matrix. -/
def e₁ : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

/-- The right-hand side `F(t, Z) = cos(2 π t) A` of the counterexample. -/
noncomputable def cexF (t : ℝ) (_ : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.cos (2 * Real.pi * t) • swapA

/-- The initial value `0 = e₁ · 0 · e₁ᵀ`. -/
noncomputable def cexY₀ : LowRank 2 2 1 where
  U := e₁
  S := 0
  V := e₁
  U_orth := by ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]
  V_orth := by ext i j; fin_cases i; fin_cases j; simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma cexF_assumption1 : Assumption1 cexF 1 1 where
  pos := one_pos
  cont Z := by
    have : Continuous fun t : ℝ => Real.cos (2 * Real.pi * t) • swapA := by fun_prop
    exact this.continuousOn
  lip t _ Z₁ Z₂ := by
    simp [cexF]

lemma capture_aug {d p : ℕ} {U₀ : Matrix (Fin d) (Fin r) ℝ} {w : Fin s → ℝ}
    {U G : Fin s → Matrix (Fin d) (Fin r) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ}
    (hQ : IsOrthOf Q (augSpace U₀ w U G)) (j : Fin s) (hj : w j ≠ 0) : Q * Qᵀ * G j = G j := by
  have h := capture_of_colSpan_le hQ.orthonormal (X := w j • G j) (by
    rw [hQ.colSpan_eq]
    exact le_sup_of_le_right (le_iSup_of_le j le_sup_right))
  rw [Matrix.mul_smul] at h
  exact smul_right_injective _ hj h

lemma eq_one_of_capture {P : Matrix (Fin 2) (Fin 2) ℝ} (h1 : P * e₁ = e₁)
    (h2 : P * (swapA * e₁) = swapA * e₁) : P = 1 := by
  have hdecomp : e₁ * e₁ᵀ + swapA * e₁ * (swapA * e₁)ᵀ = 1 := by
    have he : swapA * e₁ = !![0; 1] := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [swapA, e₁]
    rw [he]
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Fin.sum_univ_one, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp [e₁]
  calc P = P * (e₁ * e₁ᵀ + swapA * e₁ * (swapA * e₁)ᵀ) := by rw [hdecomp, Matrix.mul_one]
    _ = e₁ * e₁ᵀ + swapA * e₁ * (swapA * e₁)ᵀ := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2]
    _ = 1 := hdecomp

/-- `A` has singular values `1, 1`: `3 A` has distance at least `3` from the rank-one matrices. -/
lemma three_le_norm {Z : Matrix (Fin 2) (Fin 2) ℝ} (hZ : Z.rank ≤ 1) :
    3 ≤ ‖(-3 : ℝ) • swapA - Z‖ := by
  have hdet : Z.det = 0 := by
    by_contra h
    have hunit : IsUnit Z := (Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr h)
    have := Matrix.rank_of_isUnit Z hunit
    simp only [Fintype.card_fin] at this
    omega
  rw [Matrix.det_fin_two] at hdet
  have hsq : 9 ≤ ‖(-3 : ℝ) • swapA - Z‖ ^ 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, swapA, smul_eq_mul]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (3 + Z 0 1 + Z 1 0), sq_nonneg (Z 0 0 - Z 1 1)]
  nlinarith [norm_nonneg ((-3 : ℝ) • swapA - Z)]

lemma norm_swapA_lt : ‖swapA‖ < 3 := by
  have h : ‖swapA‖ ^ 2 = 2 := by
    rw [Frobenius.norm_sq_eq_sum]
    simp only [Fin.sum_univ_two, swapA]
    norm_num
  nlinarith [norm_nonneg swapA]

lemma boundB_cex_le (Z₀ : Matrix (Fin 2) (Fin 2) ℝ) (R : ℝ) (r : ℕ) :
    boundB cexF 1 Z₀ R r ≤ ‖swapA‖ := by
  refine Real.sSup_le ?_ (norm_nonneg _)
  rintro _ ⟨p, -, rfl⟩
  simp only [cexF, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

lemma kutta3_Cb : kutta3.Cb = 1 := by
  simp only [ExplicitRK.Cb, kutta3, Fin.sum_univ_three]
  simp
  norm_num

/-- For Kutta's method, `F = cexF`, `h = 1` and `Y₀ = 0`, the third stage has truncation error at
least `3`: the augmented bases are full, so `Ŷ_{0,3} = -F₁ + 2 F₂ = -3 A`. -/
theorem three_le_stage_error {Y : ℕ → LowRank 2 2 1} {Ys : ℕ → Fin 3 → LowRank 2 2 1}
    {Yhs : ℕ → Fin 3 → Matrix (Fin 2) (Fin 2) ℝ} {Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hsol : IsRKBUGSolution cexF kutta3 1 1 Y Ys Yhs Yh) (hY : Y 0 = cexY₀) :
    3 ≤ ‖Yhs 0 2 - (Ys 0 2).mat‖ := by
  have step := hsol 0 one_pos
  have hfirst : Ys 0 0 = cexY₀ := (step.first 0 rfl).trans hY
  obtain ⟨p, q, Uh, Vh, hU, hV, hYh, hb⟩ := step.stage 2 (by norm_num)
  have ha : kutta3.a 2 0 ≠ 0 := by simp [kutta3]
  have hF0 : cexF ((0 : ℕ) * 1 + kutta3.c 0 * 1) (Ys 0 0).mat = swapA := by
    simp [cexF, kutta3]
  have hF1 : cexF ((0 : ℕ) * 1 + kutta3.c 1 * 1) (Ys 0 1).mat = -swapA := by
    have hc : ((0 : ℕ) : ℝ) * 1 + kutta3.c 1 * 1 = 1 / 2 := by simp [kutta3]
    have hcos : Real.cos (2 * Real.pi * (1 / 2)) = -1 := by
      rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
      exact Real.cos_pi
    rw [hc]
    simp only [cexF, hcos, neg_smul, one_smul]
  have hUY : (Y 0).U = e₁ := by rw [hY]; rfl
  have hVY : (Y 0).V = e₁ := by rw [hY]; rfl
  have hUs : (Ys 0 0).U = e₁ := by rw [hfirst]; rfl
  have hVs : (Ys 0 0).V = e₁ := by rw [hfirst]; rfl
  have hsymm : swapAᵀ = swapA := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [swapA]
  have hPU : Uh * Uhᵀ = 1 := by
    refine eq_one_of_capture (capture_of_colSpan_le hU.orthonormal ?_) ?_
    · rw [hU.colSpan_eq, ← hUY]; exact le_sup_left
    · have := capture_aug hU 0 ha
      simpa only [hF0, hVs] using this
  have hPV : Vh * Vhᵀ = 1 := by
    refine eq_one_of_capture (capture_of_colSpan_le hV.orthonormal ?_) ?_
    · rw [hV.colSpan_eq, ← hVY]; exact le_sup_left
    · have := capture_aug hV 0 ha
      simpa only [hF0, hUs, hsymm] using this
  have hYmat : (Y 0).mat = 0 := by
    rw [hY]; simp [LowRank.mat, cexY₀]
  have hval : Yhs 0 2 = (-3 : ℝ) • swapA := by
    rw [hYh, hYmat, zero_add, one_smul, Fin.sum_univ_three]
    simp only [hF0, hF1]
    have hmul : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, Uh * (Uhᵀ * M * Vh) * Vhᵀ = M := fun M => by
      calc Uh * (Uhᵀ * M * Vh) * Vhᵀ = Uh * Uhᵀ * (M * (Vh * Vhᵀ)) := by
            simp only [Matrix.mul_assoc]
        _ = M := by rw [hPU, hPV, Matrix.one_mul, Matrix.mul_one]
    rw [hmul]
    have h20 : kutta3.a 2 0 = -1 := by simp [kutta3]
    have h21 : kutta3.a 2 1 = 2 := by simp [kutta3]
    have h22 : kutta3.a 2 2 = 0 := by simp [kutta3]
    rw [h20, h21, h22, zero_smul, add_zero]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    ring
  rw [hval]
  exact three_le_norm (Ys 0 2).rank_mat_le

/-- **(26) does not hold with the constant computed for (25).** Proposition 4 of arXiv 2502.07040
states (25) and (26) with one unspecified `γ̄_r`; its proof computes
`γ̄_r = √(min {n, m, 2 r s} - r) C_b B` for (25) and omits the proof of (26). That constant cannot
be reused for the stages: it fails for Kutta's third-order method with `n = m = 2`, `r = 1`,
`h = 1`, `N = 1`, `F(t, Z) = cos(2 π t) A`: Assumption 1 holds, there is an RK-BUG solution, and
the third stage violates the bound for every radius `R` in `B`. So `truncation_error` has the right
form: for the stages the constant is `∑ⱼ |a_{ij}|`. Proposition 4 as printed, with an unspecified
`γ̄_r`, holds (`truncation_error_gamma`). -/
theorem stage_bound_false_with_Cb :
    ∃ (Y : ℕ → LowRank 2 2 1) (Ys : ℕ → Fin 3 → LowRank 2 2 1)
      (Yhs : ℕ → Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (Yh : ℕ → Matrix (Fin 2) (Fin 2) ℝ),
      Assumption1 cexF 1 1 ∧ (∀ i, 0 ≤ kutta3.c i ∧ kutta3.c i ≤ 1) ∧
      IsRKBUGSolution cexF kutta3 1 1 Y Ys Yhs Yh ∧ ∀ R : ℝ,
        (1 : ℝ) * (√((min 2 (min 2 (2 * 1 * 3)) - 1 : ℕ) : ℝ) * kutta3.Cb *
          boundB cexF 1 (Y 0).mat R 1) < ‖Yhs 0 2 - (Ys 0 2).mat‖ := by
  obtain ⟨Y, Ys, Yhs, Yh, hY, hsol⟩ := exists_rkbug_solution cexF kutta3 1 1 cexY₀
  refine ⟨Y, Ys, Yhs, Yh, cexF_assumption1, fun i => ?_, hsol, fun R => ?_⟩
  · fin_cases i <;> norm_num [kutta3]
  have h1 : ((min 2 (min 2 (2 * 1 * 3)) - 1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h1, Real.sqrt_one, kutta3_Cb, one_mul, one_mul, one_mul]
  exact (boundB_cex_le _ R 1).trans_lt (norm_swapA_lt.trans_le (three_le_stage_error hsol hY))

end Counterexample

/-- The local best-approximation predicate of this file, replaced by the core
`LeanDLRA.IsBestLowRankApprox` (same definition). -/
@[deprecated (since := "2026-11-09")] alias IsBestRankApprox := LeanDLRA.IsBestLowRankApprox

end LeanDLRA.Literature.P2502_07040

import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Classical.WeylSingular
import LeanDLRA.Classical.EckartYoung
import LeanDLRA.Integrators.Matrix.Symmetry
import LeanDLRA.Matrix.LowRankDistance

/-!
# Results of arXiv 2104.05247: Rank-adaptive (augmented) BUG

Ceruti–Kusch–Lubich, *A rank-adaptive robust integrator for dynamical low-rank approximation*.
This module completes two results of the paper that the library had proved only before the final
truncation step of the algorithm.

* `exactness` (**Theorem 1**, with truncation): the truncation rule `epsRank ϑ` (smallest `r₁`
  with singular-value tail `≤ ϑ`) and the truncated SVD step `adaptiveTruncate` of the augmented
  coefficient matrix return exactly `A(t₁)` when `ϑ < σ_r(A(t₁))`, using the existing
  untruncated exactness `Exactness.augBug_exact_ode`.  The key new fact is `tailNorm_conj`
  (orthonormal bases do not change singular-value tails), combined with Eckart–Young.
* `isTwistSymm_truncation`, `augBug_truncated_isTwistSymm`, `augBug_truncated_symm`,
  `augBug_truncated_skew` (**Theorem 3**, with truncation): the truncated result of the augmented
  step stays (skew-)symmetric under an added spectral gap at the cut.  Some added hypothesis is
  needed: as printed, the skew-symmetric case of Theorem 3 fails
  (`Symmetry.augBug_trunc_not_skew`).  The untruncated statement is the existing
  `Symmetry.augBug_isTwistSymm`.

Non-vacuity examples are included.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2104_05247

open LeanDLRA.WeylSingular EckartYoung Module

section Tail

variable {p q m n : Type*} [Fintype p] [Fintype q] [Fintype m] [Fintype n]
  [DecidableEq p] [DecidableEq q] [DecidableEq n]

/-- Orthonormal factors do not change the singular-value tails. -/
theorem tailNorm_conj {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ} (hU : Uhᵀ * Uh = 1)
    (hV : Vhᵀ * Vh = 1) (S : Matrix p q ℝ) (s : ℕ) :
    tailNorm (Uh * S * Vhᵀ) s = tailNorm S s := by
  apply le_antisymm
  · have hrank : (Uh * truncation S s * Vhᵀ).rank ≤ s :=
      (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans (rank_truncation_le S s))
    refine (tailNorm_le_norm_sub _ _ hrank).trans (le_of_eq ?_)
    have : Uh * S * Vhᵀ - Uh * truncation S s * Vhᵀ = Uh * (S - truncation S s) * Vhᵀ := by
      simp [Matrix.mul_sub, Matrix.sub_mul]
    rw [this, Frobenius.norm_mul_transpose_of_orthonormal hV,
      Frobenius.norm_mul_of_orthonormal hU, tailNorm_eq_norm_sub_truncation]
  · have hrank : (Uhᵀ * truncation (Uh * S * Vhᵀ) s * Vh).rank ≤ s :=
      (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans (rank_truncation_le _ s))
    have hS : S = Uhᵀ * (Uh * S * Vhᵀ) * Vh := by
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
      simp [Matrix.mul_assoc, hV]
    refine (tailNorm_le_norm_sub _ _ hrank).trans ?_
    obtain ⟨X, hX⟩ : ∃ X, X = Uh * S * Vhᵀ := ⟨_, rfl⟩
    rw [← hX] at hS hrank ⊢
    have : S - Uhᵀ * truncation X s * Vh = Uhᵀ * (X - truncation X s) * Vh := by
      conv_lhs => rw [hS]
      simp [Matrix.mul_sub, Matrix.sub_mul]
    rw [this, tailNorm_eq_norm_sub_truncation]
    exact (norm_mul_le_of_orthonormal hV _).trans (norm_transpose_mul_le hU _)

end Tail

section Exactness

variable {m n r p q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq r] [DecidableEq p] [DecidableEq q]

/-! The rank selected by the truncation rule of the rank-adaptive BUG integrator
(arXiv 2104.05247, step 3 of the algorithm in §2.1), the smallest `r₁` such that the discarded
singular values satisfy `(∑_{i > r₁} σ_i²)^{1/2} ≤ ϑ`, is the core `ε`-rank `epsRank ϑ S` (the
smallest `r₁` with `distLR r₁ S ≤ ϑ`; the tail is that distance by `tailNorm_eq_infDist`). The
local `adaptiveRank S ϑ` of an earlier version of this file was this number (unification
batch C3). -/

/-- The truncation step of the rank-adaptive BUG integrator: the truncated SVD of the augmented
coefficient matrix `Ŝ₁` at the rank `epsRank ϑ Ŝ₁`, mapped back by the augmented bases:
`Y₁ = Û (Ŝ₁ V_{r₁} V_{r₁}ᵀ) V̂ᵀ` (the result (6) of the algorithm in §2.1). -/
noncomputable def adaptiveTruncate (Uh : Matrix m p ℝ) (Vh : Matrix n q ℝ) (S : Matrix p q ℝ)
    (ϑ : ℝ) : Matrix m n ℝ :=
  Uh * truncation S (epsRank ϑ S) * Vhᵀ

/-- **Theorem 1 (exactness) of arXiv 2104.05247, including the truncation.**
Let `F(t, Y) = Ȧ(t)` (`IsDerivRHS`), `Y₀ = U₀ S₀ V₀ᵀ = A(t₀)` with `U₀ᵀU₀ = V₀ᵀV₀ = I`, and
`A(t₁) = U S Vᵀ` with `r` columns (so `rank A(t₁) ≤ r`) and `U(t₁)ᵀU₀`, `V(t₁)ᵀV₀` invertible.
Let `K`, `L` be the K- and L-steps, `Û`, `V̂` orthonormal bases capturing `[K(t₁), U₀]` and
`[L(t₁), V₀]`, and `Ŝ` the augmented Galerkin S-step started at `Ûᵀ U₀ S₀ (V̂ᵀ V₀)ᵀ`.
If the truncation tolerance satisfies `0 ≤ ϑ < σ_r(A(t₁))` (the `r`-th largest singular value,
`singularValues` is zero-indexed), then the rank chosen by the truncation rule is exactly `r`
and the truncated result `Y₁ = Û Ŝ(t₁)_{r} V̂ᵀ` equals `A(t₁)`.

Differences from the paper: the paper assumes `rank A(t) = r` on `[t₀, t₁]`; here only the
factorization of `A(t₁)` with `r` columns is assumed (rank `≤ r`), and `ϑ < σ_r(A(t₁))` forces
rank exactly `r`.  The overlap hypotheses are stated with the integrator's starting bases `U₀`,
`V₀` in place of `U(t₀)`, `V(t₀)` (equivalent when `rank A(t₀) = r`, as in the paper).  `Û`,
`V̂` need only capture `[K(t₁), U₀]`, `[L(t₁), V₀]` (their range may be larger).  The tolerance is
assumed nonnegative.  The truncation is the Eckart--Young truncated SVD
`EckartYoung.truncation` of `Ŝ(t₁)`; the rank rule is the `ε`-rank `epsRank ϑ`. -/
theorem exactness {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {A : ℝ → Matrix m n ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁)
    {U₀ : Matrix m r ℝ} {S₀ : Matrix r r ℝ} {V₀ : Matrix n r ℝ}
    (hU₀ : U₀ᵀ * U₀ = 1) (hV₀ : V₀ᵀ * V₀ = 1) (hY₀ : U₀ * S₀ * V₀ᵀ = A t₀)
    {U : Matrix m r ℝ} {S : Matrix r r ℝ} {V : Matrix n r ℝ} (hA₁ : A t₁ = U * S * Vᵀ)
    (hU : IsUnit (Uᵀ * U₀)) (hV : IsUnit (Vᵀ * V₀))
    {K : ℝ → Matrix m r ℝ} (hK : ODESolution (fun t K => F t (K * V₀ᵀ) * V₀) K t₀ t₁)
    (hK₀ : K t₀ = U₀ * S₀)
    {L : ℝ → Matrix n r ℝ} (hL : ODESolution (fun t L => (F t (U₀ * Lᵀ))ᵀ * U₀) L t₀ t₁)
    (hL₀ : L t₀ = V₀ * S₀ᵀ)
    {Uh : Matrix m p ℝ} {Vh : Matrix n q ℝ} (hUo : Uhᵀ * Uh = 1) (hVo : Vhᵀ * Vh = 1)
    (hUh : Uh * Uhᵀ * Matrix.fromCols (K t₁) U₀ = Matrix.fromCols (K t₁) U₀)
    (hVh : Vh * Vhᵀ * Matrix.fromCols (L t₁) V₀ = Matrix.fromCols (L t₁) V₀)
    {Sf : ℝ → Matrix p q ℝ}
    (hSf : ODESolution (fun t S => Uhᵀ * F t (Uh * S * Vhᵀ) * Vh) Sf t₀ t₁)
    (hSf₀ : Sf t₀ = Uhᵀ * U₀ * S₀ * (Vhᵀ * V₀)ᵀ)
    {ϑ : ℝ} (hϑ0 : 0 ≤ ϑ)
    (hϑ : ϑ < (Matrix.toEuclideanLin (A t₁)).singularValues (Fintype.card r - 1)) :
    epsRank ϑ (Sf t₁) = Fintype.card r ∧ adaptiveTruncate Uh Vh (Sf t₁) ϑ = A t₁ := by
  have hX : Uh * Sf t₁ * Vhᵀ = A t₁ :=
    Exactness.augBug_exact_ode ht hA hU₀ hV₀ hY₀ hA₁ hU hV hK hK₀ hL hL₀ hUh hVh hSf hSf₀
  have htail : ∀ s, tailNorm (Sf t₁) s = tailNorm (A t₁) s := fun s => by
    rw [← hX, tailNorm_conj hUo hVo]
  have hrank : (A t₁).rank ≤ Fintype.card r := by
    rw [hA₁]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_width _))
  have hmem : Fintype.card r ∈ {s : ℕ | tailNorm (Sf t₁) s ≤ ϑ} := by
    change tailNorm (Sf t₁) _ ≤ ϑ
    rw [htail]
    refine (tailNorm_le_norm_sub (A t₁) (A t₁) hrank).trans ?_
    simpa using hϑ0
  have hlow : ∀ s ∈ {s : ℕ | tailNorm (Sf t₁) s ≤ ϑ}, Fintype.card r ≤ s := by
    intro s hs
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have hs' : tailNorm (A t₁) s ≤ ϑ := by rw [← htail]; exact hs
    set T := Matrix.toEuclideanLin (A t₁)
    have hpos : 0 < T.singularValues (Fintype.card r - 1) := lt_of_le_of_lt hϑ0 hϑ
    have hcn : Fintype.card r - 1 < Fintype.card n := by
      by_contra hge'
      have hge := not_lt.mp hge'
      have : finrank ℝ (EuclideanSpace ℝ n) ≤ Fintype.card r - 1 := by
        simpa using hge
      exact hpos.ne' (T.singularValues_of_finrank_le this)
    have hsn : s < Fintype.card n := by omega
    have hterm : T.singularValues s ^ 2 ≤ ∑ l ∈ Ico s (Fintype.card n), T.singularValues l ^ 2 :=
      Finset.single_le_sum (f := fun l => T.singularValues l ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_Ico.2 ⟨le_rfl, hsn⟩)
    have hge : ϑ < T.singularValues s :=
      hϑ.trans_le (T.singularValues_antitone (by omega))
    have : T.singularValues s ≤ tailNorm (A t₁) s := by
      unfold tailNorm
      exact Real.le_sqrt_of_sq_le hterm
    linarith
  have hset : {s : ℕ | distLR s (Sf t₁) ≤ ϑ} = {s : ℕ | tailNorm (Sf t₁) s ≤ ϑ} := by
    simp only [distLR, lowRankSet, ← tailNorm_eq_infDist]
  have hr1 : epsRank ϑ (Sf t₁) = Fintype.card r := by
    rw [epsRank, hset]
    exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlow)
  refine ⟨hr1, ?_⟩
  have h0 : tailNorm (Sf t₁) (Fintype.card r) = 0 :=
    le_antisymm (by rw [htail]; exact (tailNorm_le_norm_sub (A t₁) (A t₁) hrank).trans (by simp))
      (tailNorm_nonneg _ _)
  have htr : truncation (Sf t₁) (Fintype.card r) = Sf t₁ := by
    rw [tailNorm_eq_norm_sub_truncation, norm_eq_zero, sub_eq_zero] at h0
    exact h0.symm
  unfold adaptiveTruncate
  rw [hr1, htr, hX]

/-- **Non-vacuity of `exactness`.**  A `1 × 1` instance: `F ≡ 1`, `A(t) = 1 + t`, `t₀ = 0`,
`t₁ = 1`, all bases `= 1`, tolerance `ϑ = 0`.  All hypotheses of `exactness` are satisfied (the
ODE solutions are affine), so the rank selected is `1`. -/
example : ∃ (A : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (Sf : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    A 1 ≠ 0 ∧ epsRank 0 (Sf 1) = 1 ∧ adaptiveTruncate 1 1 (Sf 1) 0 = A 1 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 1) (Fin 1) ℝ, M = 1 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → Matrix (Fin 1) (Fin 1) ℝ, A = fun t => M + (t - 0) • M :=
    ⟨_, rfl⟩
  have hode : ∀ f : ℝ → Matrix (Fin 1) (Fin 1) ℝ → Matrix (Fin 1) (Fin 1) ℝ,
      (∀ t x, f t x = M) → ODESolution f (fun t => M + (t - 0) • M) 0 1 := fun f hf => by
    have : f = fun _ _ => M := funext₂ hf
    subst this
    exact Symmetry.odeSolution_affine M M 0 1
  have hA : IsDerivRHS (fun _ _ => M) A 0 1 := by
    subst hAdef
    exact ⟨(Symmetry.odeSolution_affine M M 0 1).cont,
      fun t ht _ => (Symmetry.odeSolution_affine M M 0 1).deriv t ht⟩
  have hA1 : A 1 = (2 : ℝ) • M := by rw [hAdef]; simp [two_smul]
  have hA0 : A 0 = M := by rw [hAdef]; simp
  have hMM : M * M = M := by rw [hM]; simp
  have hMt : Mᵀ = M := by rw [hM]; simp
  have hM1 : M = (1 : Matrix (Fin 1) (Fin 1) ℝ) := hM
  have h := exactness (F := fun _ _ => M) (A := A) (t₀ := 0) (t₁ := 1) zero_le_one hA
    (U₀ := M) (S₀ := M) (V₀ := M) (by rw [hMt, hMM]; exact hM) (by rw [hMt, hMM]; exact hM)
    (by rw [hMt, hMM, hMM, hA0])
    (U := M) (S := (2 : ℝ) • M) (V := M)
    (by rw [hA1, Matrix.mul_smul, Matrix.smul_mul, hMt, hMM, hMM])
    (by rw [hMt, hMM]; rw [hM]; exact isUnit_one) (by rw [hMt, hMM]; rw [hM]; exact isUnit_one)
    (K := fun t => M + (t - 0) • M) (hode _ (fun t x => by rw [hMM]))
    (by simp [hMM]) (L := fun t => M + (t - 0) • M) (hode _ (fun t x => by rw [hMt, hMM]))
    (by simp [hMM, hMt])
    (Uh := M) (Vh := M) (by rw [hMt, hMM]; exact hM) (by rw [hMt, hMM]; exact hM)
    (by subst hM; ext i j; rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.mul_apply])
    (by subst hM; ext i j; rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.mul_apply])
    (Sf := fun t => M + (t - 0) • M) (hode _ (fun t x => by rw [hMt, hMM, hMM]))
    (by simp [hMt, hMM])
    (ϑ := 0) le_rfl ?_
  · rw [hM] at h
    have hne : A 1 ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 0) 0
      rw [hA1, hM] at this
      simp at this
    exact ⟨A, fun t => 1 + (t - 0) • 1, hne, by simpa using h.1, h.2⟩
  · have hne : A 1 ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 0) 0
      rw [hA1, hM] at this
      simp at this
    have hr : 0 < (A 1).rank := by
      rw [Matrix.rank_of_det_ne_zero (by rw [hA1, hM]; simp)]
      simp
    rw [rank_eq_finrank_range] at hr
    simpa using (LinearMap.singularValues_pos_iff_lt_finrank_range
      (T := Matrix.toEuclideanLin (A 1)) (n := 0)).2 hr

end Exactness

section Symmetric

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **A gapped truncation of a `σ`-symmetric matrix is `σ`-symmetric.**  If `Ŝᵀ = σ Ŝ` with
`σ = ±1` and `σ_s(Ŝ) < σ_{s-1}(Ŝ)` (or `s = 0`), then the truncated SVD `Ŝ V_s V_sᵀ`
(`EckartYoung.truncation`) satisfies `(Ŝ V_s V_sᵀ)ᵀ = σ Ŝ V_s V_sᵀ`.  (Reason: the span of the
top `s` right singular vectors is `Ŝ`-invariant when there is a gap, so the orthogonal projector
onto it commutes with `Ŝ`.) -/
theorem isTwistSymm_truncation {σ : ℝ} (hσ : σ * σ = 1) {S : Matrix k k ℝ}
    (hS : Symmetry.IsTwistSymm σ S) (s : ℕ)
    (hgap : 0 < s → (Matrix.toEuclideanLin S).singularValues s <
      (Matrix.toEuclideanLin S).singularValues (s - 1)) :
    Symmetry.IsTwistSymm σ (truncation S s) := by
  set T := Matrix.toEuclideanLin S with hTdef
  set e := rightSingularVectors S with he
  have hadjT : LinearMap.adjoint T = σ • T := by
    have h1 : LinearMap.adjoint T = Matrix.toEuclideanLin Sᵀ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [h1, hS]
    exact map_smul _ _ _
  -- self-adjointness up to the sign `σ`
  have hadj : ∀ x y : EuclideanSpace ℝ k, ⟪T x, y⟫ = σ * ⟪x, T y⟫ := by
    intro x y
    rw [← LinearMap.adjoint_inner_right T x y, hadjT]
    simp [real_inner_smul_right]
  -- eigen-relation `σ T² e_i = σ_i² e_i`
  have heig : ∀ i, σ • T (T (e i)) = (T.singularValues i ^ 2) • e i := by
    intro i
    have := adjoint_toEuclideanLin_rightSingularVectors S i
    rw [hadjT] at this
    simpa using this
  -- the projector `Π`
  set P : EuclideanSpace ℝ k → EuclideanSpace ℝ k := fun x =>
    ∑ i ∈ univ.filter fun i : Fin (finrank ℝ (EuclideanSpace ℝ k)) ↦ (i : ℕ) < s,
      ⟪e i, x⟫ • e i with hP
  have hPin : ∀ l x, ⟪e l, P x⟫ = if (l : ℕ) < s then ⟪e l, x⟫ else 0 :=
    fun l x => inner_rightSingularVectors_sum S s x l
  have hPsa : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫ := by
    intro x y
    simp only [hP, sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (e i)]
    ring
  -- orthogonality across the gap
  have hc : ∀ l j : Fin (finrank ℝ (EuclideanSpace ℝ k)), ((l : ℕ) < s ↔ ¬ (j : ℕ) < s) →
      ⟪e l, T (e j)⟫ = 0 := by
    have heig' : ∀ i, T (T (e i)) = (σ * T.singularValues i ^ 2) • e i := by
      intro i
      have h := congrArg (fun v => σ • v) (heig i)
      simp only [smul_smul, hσ, one_smul] at h
      exact h
    have hμ : ∀ a b : Fin (finrank ℝ (EuclideanSpace ℝ k)), (a : ℕ) < s → ¬ (b : ℕ) < s →
        T.singularValues b ^ 2 < T.singularValues a ^ 2 := by
      intro a b ha hb
      have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) ha
      have h1 := hgap hs
      have h2 : T.singularValues (s - 1) ≤ T.singularValues a :=
        T.singularValues_antitone (by omega)
      have h3 : T.singularValues b ≤ T.singularValues s :=
        T.singularValues_antitone (by omega)
      have h4 := T.singularValues_nonneg b
      nlinarith
    have key : ∀ a b : Fin (finrank ℝ (EuclideanSpace ℝ k)),
        σ * (T.singularValues a ^ 2 - T.singularValues b ^ 2) * ⟪e a, T (e b)⟫ = 0 := by
      intro a b
      have h1 : ⟪T (T (e a)), T (e b)⟫ = σ * ⟪T (e a), T (T (e b))⟫ := hadj _ _
      rw [heig' a, heig' b, inner_smul_left, inner_smul_right, hadj (e a) (e b)] at h1
      simp only [conj_trivial] at h1
      linear_combination h1 + (σ * T.singularValues b ^ 2 * ⟪e a, T (e b)⟫) * hσ
    intro l j hlj
    have hne : T.singularValues l ^ 2 - T.singularValues j ^ 2 ≠ 0 ∨
        T.singularValues j ^ 2 - T.singularValues l ^ 2 ≠ 0 := by
      by_cases hl : (l : ℕ) < s
      · left
        have := hμ l j hl (hlj.mp hl)
        linarith
      · right
        have hj : (j : ℕ) < s := by
          by_contra hj
          exact hl (hlj.mpr hj)
        have := hμ j l hj hl
        linarith
    have hσ0 : σ ≠ 0 := by
      intro h0
      rw [h0] at hσ
      simp at hσ
    rcases hne with hne | hne
    · have := key l j
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero hσ0 hne)
      · exact h
    · have h0 : ⟪e j, T (e l)⟫ = 0 := by
        rcases mul_eq_zero.1 (key j l) with h | h
        · exact absurd h (mul_ne_zero hσ0 hne)
        · exact h
      have h1 := hadj (e l) (e j)
      rw [real_inner_comm (e j) (T (e l)), h0] at h1
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hσ0
      · exact h
  have hext : ∀ x y : EuclideanSpace ℝ k, (∀ l, ⟪e l, x⟫ = ⟪e l, y⟫) → x = y := by
    intro x y h
    rw [← e.sum_repr' x, ← e.sum_repr' y]
    exact Finset.sum_congr rfl fun l _ => by rw [h l]
  have hbk : ∀ (l : Fin (finrank ℝ (EuclideanSpace ℝ k))) z,
      ⟪e l, T z⟫ = σ * ⟪T (e l), z⟫ := by
    intro l z
    rw [hadj (e l) z, ← mul_assoc, hσ, one_mul]
  have hPT : ∀ j : Fin (finrank ℝ (EuclideanSpace ℝ k)),
      P (T (e j)) = if (j : ℕ) < s then T (e j) else 0 := by
    intro j
    refine hext _ _ fun l => ?_
    rw [hPin]
    by_cases hl : (l : ℕ) < s <;> by_cases hj : (j : ℕ) < s
    · simp only [hl, hj, ↓reduceIte]
    · simp only [hl, hj, ↓reduceIte, inner_zero_right]
      exact hc l j (by simp [hl, hj])
    · simp only [hl, hj, ↓reduceIte]
      exact (hc l j (by simp [hl, hj])).symm
    · simp only [hl, hj, ↓reduceIte, inner_zero_right]
  have hcomm : ∀ y, P (T y) = T (P y) := by
    intro y
    refine hext _ _ fun l => ?_
    rw [hPin, hbk l (P y), ← hPsa, hPT]
    by_cases hl : (l : ℕ) < s
    · simp [hl, hbk l y]
    · simp [hl]
  unfold Symmetry.IsTwistSymm
  apply (Matrix.toEuclideanLin (m := k) (n := k) (𝕜 := ℝ)).injective
  have hTr : ∀ x, Matrix.toEuclideanLin (truncation S s) x = T (P x) :=
    toEuclideanLin_truncation_apply S s
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, map_smul]
  ext1 y
  refine ext_inner_right ℝ fun x => ?_
  have hbk2 : ∀ y z : EuclideanSpace ℝ k, ⟪y, T z⟫ = σ * ⟪T y, z⟫ := by
    intro y z
    rw [hadj y z, ← mul_assoc, hσ, one_mul]
  rw [LinearMap.adjoint_inner_left, LinearMap.smul_apply, inner_smul_left, hTr, hTr, hbk2 y (P x),
    ← hPsa, hcomm]
  simp only [conj_trivial]


/-- **Non-vacuity of the gap hypothesis.**  For the symmetric matrix `S = 1 ∈ ℝ^{1×1}` and the
cut `s = 1 > 0`, the gap `σ_1 < σ_0` holds, so `isTwistSymm_truncation` applies with a positive
rank (the instance of the dynamics is the one of `Symmetry`'s examples). -/
example : (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues 1 <
    (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues (1 - 1) := by
  set T := Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)
  have h1 : T.singularValues 1 = 0 :=
    T.singularValues_of_finrank_le (by simp)
  have hr : 0 < (1 : Matrix (Fin 1) (Fin 1) ℝ).rank := by simp
  rw [rank_eq_finrank_range] at hr
  have h0 : 0 < T.singularValues 0 :=
    (LinearMap.singularValues_pos_iff_lt_finrank_range (T := T) (n := 0)).2 hr
  simpa [h1] using h0

end Symmetric

section SymmetryPreservation

variable {n r p : Type*} [Fintype n] [Fintype r] [Fintype p] [DecidableEq p]
  {σ L : ℝ} {F : ℝ → Matrix n n ℝ → Matrix n n ℝ} {t₀ t₁ : ℝ}

/-- **Theorem 3 of arXiv 2104.05247 (`σ`-symmetry preservation), including the truncation.**
`σ = 1` is the symmetric case and `σ = -1` the skew-symmetric case; the hypothesis is the
equivariance `F(t, σ Yᵀ) = σ F(t, Y)ᵀ`, which is equivalent to condition (10) resp. (11) of the
paper (see `Symmetry.isTwistEquivariant_one_iff`, `Symmetry.isTwistEquivariant_neg_one_iff`).
The K- and L-steps use the basis `U₀`, `Û` captures `K(t₁)` and `V̂ = Û` (a valid choice, since
`L(t₁) = σ K(t₁)`), the augmented S-step starts at `M̂ S₀ M̂ᵀ` (`M̂ = Ûᵀ U₀`), and `Y₁` is the
truncation of `Ŝ(t₁)` at the rank selected by the rule `epsRank ϑ` with tolerance `ϑ`.  Then
`Y₁ = Û Ŝ(t₁)_{r₁} Ûᵀ` is `σ`-symmetric.

The untruncated part (`Ŷ₁ = Û Ŝ(t₁) Ûᵀ` is `σ`-symmetric) is `Symmetry.augBug_isTwistSymm`.
Differences from the paper: the paper claims the truncated result is (skew-)symmetric without
qualification.  For `σ = -1` that is false (`Symmetry.augBug_trunc_not_skew`: the rank rule can
select an odd rank, and no odd-rank matrix is skew-symmetric); for `σ = 1` a tie of singular
values at the cut makes the truncated SVD non-unique, and symmetry then depends on the choice of
singular vectors (not formalized).  We therefore assume a spectral gap at the cut,
`σ_{r₁}(Ŝ(t₁)) < σ_{r₁-1}(Ŝ(t₁))` whenever `r₁ > 0`, which suffices for the truncation to preserve
the structure (`isTwistSymm_truncation`).  `F` is also assumed Lipschitz (for uniqueness of the
substep solutions, which the paper's proof via [1, Theorem 5] uses implicitly). -/
theorem augBug_truncated_isTwistSymm (hσ : σ * σ = 1) (hF : Symmetry.IsTwistEquivariant σ F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ}
    (hS₀ : Symmetry.IsTwistSymm σ S₀) {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (Symmetry.kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (Symmetry.lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {Û : Matrix n p ℝ} (hcap : Û * Ûᵀ * K t₁ = K t₁)
    {Ŝ : ℝ → Matrix p p ℝ} (hS : ODESolution (Symmetry.sField Û Û F) Ŝ t₀ t₁)
    (hS0 : Ŝ t₀ = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) {ϑ : ℝ}
    (hgap : 0 < epsRank ϑ (Ŝ t₁) →
      (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁)) <
        (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁) - 1)) :
    Symmetry.IsTwistSymm σ (adaptiveTruncate Û Û (Ŝ t₁) ϑ) := by
  have h := Symmetry.augBug_isTwistSymm hσ hF hL hS₀ hK hK0 hLs hL0 hcap hS hS0 ht
  exact (isTwistSymm_truncation hσ h.2.2.1 _ hgap).mul_mul_transpose Û

/-- **Theorem 3 of arXiv 2104.05247, symmetric case, with truncation** (condition (10),
`F(t, Y)ᵀ = F(t, Yᵀ)`, in the equivalent form `F(t, Yᵀ)ᵀ = F(t, Y)`; `S₀` symmetric).  See
`augBug_truncated_isTwistSymm` for the spectral-gap and Lipschitz hypotheses. -/
theorem augBug_truncated_symm (hF : Symmetry.SymmCondition F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : S₀.IsSymm)
    {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (Symmetry.kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (Symmetry.lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {Û : Matrix n p ℝ} (hcap : Û * Ûᵀ * K t₁ = K t₁)
    {Ŝ : ℝ → Matrix p p ℝ} (hS : ODESolution (Symmetry.sField Û Û F) Ŝ t₀ t₁)
    (hS0 : Ŝ t₀ = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) {ϑ : ℝ}
    (hgap : 0 < epsRank ϑ (Ŝ t₁) →
      (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁)) <
        (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁) - 1)) :
    (adaptiveTruncate Û Û (Ŝ t₁) ϑ).IsSymm :=
  (Symmetry.isTwistSymm_one_iff _).1 <|
    augBug_truncated_isTwistSymm (by norm_num) ((Symmetry.isTwistEquivariant_one_iff F).2 hF) hL
      ((Symmetry.isTwistSymm_one_iff S₀).2 hS₀) hK hK0 hLs hL0 hcap hS hS0 ht hgap

/-- **Theorem 3 of arXiv 2104.05247, skew-symmetric case, with truncation** (condition (11),
`F(t, Y)ᵀ = -F(t, -Yᵀ)`, in the equivalent form `F(t, Yᵀ)ᵀ = -F(t, -Y)`; `S₀ᵀ = -S₀`).  See
`augBug_truncated_isTwistSymm`; some added hypothesis such as the spectral gap is needed here,
since without it the claim is false (`Symmetry.augBug_trunc_not_skew`). -/
theorem augBug_truncated_skew (hF : Symmetry.SkewCondition F)
    (hL : IsLipschitzField F L) {U₀ : Matrix n r ℝ} {S₀ : Matrix r r ℝ} (hS₀ : S₀ᵀ = -S₀)
    {K Lf : ℝ → Matrix n r ℝ}
    (hK : ODESolution (Symmetry.kField U₀ F) K t₀ t₁) (hK0 : K t₀ = U₀ * S₀)
    (hLs : ODESolution (Symmetry.lField U₀ F) Lf t₀ t₁) (hL0 : Lf t₀ = U₀ * S₀ᵀ)
    {Û : Matrix n p ℝ} (hcap : Û * Ûᵀ * K t₁ = K t₁)
    {Ŝ : ℝ → Matrix p p ℝ} (hS : ODESolution (Symmetry.sField Û Û F) Ŝ t₀ t₁)
    (hS0 : Ŝ t₀ = Ûᵀ * U₀ * S₀ * (Ûᵀ * U₀)ᵀ) (ht : t₀ ≤ t₁) {ϑ : ℝ}
    (hgap : 0 < epsRank ϑ (Ŝ t₁) →
      (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁)) <
        (Matrix.toEuclideanLin (Ŝ t₁)).singularValues (epsRank ϑ (Ŝ t₁) - 1)) :
    (adaptiveTruncate Û Û (Ŝ t₁) ϑ)ᵀ = -adaptiveTruncate Û Û (Ŝ t₁) ϑ :=
  (Symmetry.isTwistSymm_neg_one_iff _).1 <|
    augBug_truncated_isTwistSymm (by norm_num) ((Symmetry.isTwistEquivariant_neg_one_iff F).2 hF)
      hL ((Symmetry.isTwistSymm_neg_one_iff S₀).2 hS₀) hK hK0 hLs hL0 hcap hS hS0 ht hgap

end SymmetryPreservation

end LeanDLRA.Literature.P2104_05247

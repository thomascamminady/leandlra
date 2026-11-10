import LeanDLRA.OpenProblems.TensorNetworks.Part1Defs
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Integrators.TuckerBUG
import LeanDLRA.Integrators.Exactness
import LeanDLRA.Integrators.RankAdaptiveBUG
import LeanDLRA.Classical.CommutingProjectorTelescoping
import LeanDLRA.Matrix.Orthonormal
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Tensor.TTN.Abstract.ProjectorSplittingExactness

/-!
# Open problems OP-TN-03, OP-TN-04, OP-TN-05

The exactness theorem of OP-TN-05 (`tucker_ksl_exact`) is in
`LeanDLRA/Tensor/TTN/Abstract/ProjectorSplittingExactness.lean`.
-/

open Set Finset
open scoped RealInnerProductSpace

universe u

namespace LeanDLRA.OpenProblems.TensorNetworks

open LeanDLRA

section NestedKSL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end NestedKSL

section TTN

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end TTN

section Defect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Defect

section Factored

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- OP-TN-03 (source: arXiv 1709.02594, §5, assumptions (24)–(25) and proof of Thm 4), matrix
case.  If the normal component of `F` with respect to the tangent space of the rank-`r` manifold
is at most `ε` at every point `U S Vᵀ` of rank exactly `r` (`S` invertible), and `F` is
Lipschitz, then the factored (doubly-normal) bound `‖(1 - U Uᵀ) F(t, Y) (1 - V Vᵀ)‖ ≤ ε` also
holds at the rank-deficient points `Y = U S Vᵀ` (`S` singular), such as the `K`-step end points
`U₁ S V₀ᵀ`.  (The Tucker version perturbs the core by a core whose matricizations all have full
rank, which exists iff `rᵢ ≤ ∏_{j ≠ i} rⱼ`.) -/
theorem factored_normal_of_manifold_normal {r : ℕ} {F : ℝ → Matrix m n ℝ → Matrix m n ℝ}
    {L ε : ℝ} (hF : IsLipschitzField F L)
    (hM : ∀ t (U : Matrix m (Fin r) ℝ) (V : Matrix n (Fin r) ℝ) (S : Matrix (Fin r) (Fin r) ℝ),
      Uᵀ * U = 1 → Vᵀ * V = 1 → IsUnit S.det →
        ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε)
    (t : ℝ) {U : Matrix m (Fin r) ℝ} {V : Matrix n (Fin r) ℝ} (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (S : Matrix (Fin r) (Fin r) ℝ) :
    ‖(1 - U * Uᵀ) * F t (U * S * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
  have hFc : Continuous (F t) := by
    have hF' : IsLipschitzField F (max L 0) := fun t x y =>
      (hF t x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    exact (hF'.lipschitzWith (le_max_right _ _) t).continuous
  have hG : Continuous fun δ : ℝ =>
      ‖(1 - U * Uᵀ) * F t (U * (S + δ • 1) * Vᵀ) * (1 - V * Vᵀ)‖ := by
    have : Continuous fun δ : ℝ => U * (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ)) * Vᵀ := by
      fun_prop
    have h2 := hFc.comp this
    fun_prop
  set Z : Set ℝ := {δ : ℝ | Polynomial.IsRoot (Matrix.charpoly (-S)) δ} with hZ
  have hfin : Z.Finite :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-S)).ne_zero
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) {0}ᶜ, δ ∉ Z := by
    have hcl : IsClosed (Z \ {0}) :=
      (hfin.subset Set.sdiff_subset).isClosed
    have h1 : ∀ᶠ δ in nhds (0 : ℝ), δ ∉ (Z \ {0}) :=
      hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with δ h2 h3
    intro h4
    exact h2 ⟨h4, h3⟩
  have hle : ∀ᶠ δ in nhdsWithin (0 : ℝ) {0}ᶜ,
      ‖(1 - U * Uᵀ) * F t (U * (S + δ • 1) * Vᵀ) * (1 - V * Vᵀ)‖ ≤ ε := by
    filter_upwards [hev] with δ hδ
    refine hM t U V (S + δ • 1) hU hV ?_
    have hdet : (S + δ • (1 : Matrix (Fin r) (Fin r) ℝ)).det =
        (Matrix.charpoly (-S)).eval δ := by
      rw [Matrix.eval_charpoly, sub_neg_eq_add, add_comm]
      simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hdet, isUnit_iff_ne_zero]
    exact hδ
  have := le_of_tendsto (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hle
  simpa using this

end Factored

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- OP-TN-04 (source: arXiv 2603.13990 §6.1; Oseledets 2011, Thm 2.2), TT-SVD error identity.
Sequential truncations `x (k+1) = R k (x k)` by orthogonal projectors with *decreasing ranges*
(`range R j ⊆ range R k` for `k ≤ j`, as for the left interface projectors `P_{≤k} ⊗ I` of a TT-SVD
sweep) have mutually orthogonal increments, so the total error is the root of the sum of squares
of the per-bond errors: `‖x 0 - x K‖² = ∑_{k < K} ‖x k - R k (x k)‖²`.  The existing chain lemma
`norm_sub_le_of_chain` only gives the sum of the per-bond errors. -/
theorem ttsvd_norm_sq_sub_eq {R : ℕ → E →L[ℝ] E} (hR : ∀ k, IsOrthProj (R k))
    (hnest : ∀ k j, k ≤ j → ∀ y, R k (R j y) = R j y) {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = R k (x k)) (K : ℕ) :
    ‖x 0 - x K‖ ^ 2 = ∑ k ∈ range K, ‖x k - R k (x k)‖ ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    set y : E := x K - R K (x K) with hy
    have hRy : ∀ j < K, R j y = y := by
      intro j hj
      have h1 : R j (x K) = x K := by
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
        rw [hx k]
        exact hnest j k (by omega) (x k)
      rw [hy, map_sub, h1, hnest j K hj.le (x K)]
    have hsum : x 0 - x K = ∑ j ∈ range K, (x j - R j (x j)) := by
      have := Finset.sum_range_sub' x K
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx j]
    have horth : ⟪x 0 - x K, y⟫ = 0 := by
      rw [hsum, sum_inner]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [inner_sub_left, (hR j).symm, hRy j (Finset.mem_range.1 hj), sub_self]
    have hdec : x 0 - x (K + 1) = (x 0 - x K) + y := by
      rw [hx K, hy]; abel
    rw [hdec, norm_add_sq_real, horth]
    ring

/-- OP-TN-04 (source: arXiv 2603.13990, Conclusion and Fig. 5), per-bond thresholds.  Under the
hypotheses of `ttsvd_norm_sq_sub_eq`, per-bond truncation errors `≤ τ / √K` give the global
tolerance `τ` after `K = N - 1` bonds; per-bond thresholds `τ` only give `√K τ`, which is the
proposed explanation of the bond-dimension growth with the number of qubits. -/
theorem ttsvd_norm_sub_le_of_tol {R : ℕ → E →L[ℝ] E} (hR : ∀ k, IsOrthProj (R k))
    (hnest : ∀ k j, k ≤ j → ∀ y, R k (R j y) = R j y) {x : ℕ → E}
    (hx : ∀ k, x (k + 1) = R k (x k)) {K : ℕ} (hK : 0 < K) {τ : ℝ}
    (htol : ∀ k < K, ‖x k - R k (x k)‖ ≤ τ / √(K : ℝ)) :
    ‖x 0 - x K‖ ≤ τ := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < √(K : ℝ) := Real.sqrt_pos.2 hKpos
  have hτ : 0 ≤ τ := by
    have := (norm_nonneg _).trans (htol 0 hK)
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hs)
  rw [← abs_of_nonneg (norm_nonneg (x 0 - x K)), ← abs_of_nonneg hτ]
  refine sq_le_sq.1 ?_
  rw [ttsvd_norm_sq_sub_eq hR hnest hx K]
  calc ∑ k ∈ range K, ‖x k - R k (x k)‖ ^ 2 ≤ ∑ k ∈ range K, (τ / √(K : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun k hk =>
          pow_le_pow_left₀ (norm_nonneg _) (htol k (Finset.mem_range.1 hk)) 2
    _ = τ ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow, Real.sq_sqrt hKpos.le]
        field_simp

/-- OP-TN-04 (source: arXiv 2203.08455 §5), constants of tensor low-rank Parareal: a
`κ`-quasi-optimal truncation `T` (`‖T y - y‖ ≤ κ dist(y, M)`, `κ = √d` for HOSVD, `√(d-1)` for
TT-SVD) satisfies `‖T y - X‖ ≤ (1 + κ) ‖y - X‖` for every `X ∈ M`; this replaces the
best-approximation constant `2` in the matrix Parareal recursion. -/
theorem quasiOpt_trunc_norm_sub_le {T : E → E} {M : Set E} {κ : ℝ} (hκ : 0 ≤ κ)
    (hT : ∀ y, ‖T y - y‖ ≤ κ * Metric.infDist y M) {X : E} (hX : X ∈ M) (y : E) :
    ‖T y - X‖ ≤ (1 + κ) * ‖y - X‖ := by
  have _ : InnerProductSpace ℝ E := inferInstance
  have h1 : Metric.infDist y M ≤ ‖y - X‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hX
  calc ‖T y - X‖ = ‖(T y - y) + (y - X)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖T y - y‖ + ‖y - X‖ := norm_add_le _ _
    _ ≤ κ * ‖y - X‖ + ‖y - X‖ := by gcongr; exact (hT y).trans (by gcongr)
    _ = (1 + κ) * ‖y - X‖ := by ring

end Truncation

section Counterexample

open scoped Matrix LeanDLRA.Frobenius

private theorem cx_eq_smul (t : ℝ) : cxA t = Real.cos t • !![(0 : ℝ), 0; 1, 0] +
    Real.sin t • !![(0 : ℝ), 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxA]

private theorem cxdot_eq_smul (t : ℝ) : cxAdot t = (-Real.sin t) • !![(0 : ℝ), 0; 1, 0] +
    Real.cos t • !![(0 : ℝ), 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]

private theorem cx_isDerivRHS :
    IsDerivRHS (fun t _ => cxAdot t) cxA 0 (Real.pi / 2) := by
  have hd : ∀ t : ℝ, HasDerivAt cxA (cxAdot t) t := by
    intro t
    have h := ((Real.hasDerivAt_cos t).smul_const !![(0 : ℝ), 0; 1, 0]).add
      ((Real.hasDerivAt_sin t).smul_const !![(0 : ℝ), 0; 0, 1])
    have e : cxA = fun t => Real.cos t • !![(0 : ℝ), 0; 1, 0] +
        Real.sin t • !![(0 : ℝ), 0; 0, 1] := funext cx_eq_smul
    rw [e, cxdot_eq_smul]
    exact h
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt,
    fun t _ _ => (hd t).hasDerivWithinAt⟩

private theorem cx_colspace (t : ℝ) : ce₂ * (ce₂ᵀ * cxA t) = cxA t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxA, ce₂, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem cx_not_recoverable :
    ¬ Exactness.IsRecoverable Exactness.leftMulClass (rightProj ce₁) (cxA (Real.pi / 2)) := by
  rintro ⟨T, -, hT⟩
  have h0 : rightProj ce₁ (cxA (Real.pi / 2)) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cxA, ce₁, Matrix.mul_apply]
  rw [h0, map_zero] at hT
  have := congrFun (congrFun hT 1) 1
  simp [cxA] at this

private theorem cx_odeSolution_zero {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : ℝ → E' → E'} (hf : ∀ t, f t 0 = 0) (a b : ℝ) : ODESolution f (fun _ => 0) a b :=
  ⟨continuousOn_const, fun t _ => by rw [hf]; exact hasDerivWithinAt_const t _ 0⟩

private theorem leftProj_ce₁ (M : Matrix (Fin 2) (Fin 2) ℝ) :
    leftProj ce₁ M = !![M 0 0, M 0 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ce₁, Matrix.mul_apply, Matrix.vecMul, dotProduct]

private theorem rightProj_ce₁ (M : Matrix (Fin 2) (Fin 2) ℝ) :
    rightProj ce₁ M = !![M 0 0, 0; M 1 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ce₁, Matrix.mul_apply]

private theorem rightProj_ce₂ (M : Matrix (Fin 2) (Fin 2) ℝ) :
    rightProj ce₂ M = !![0, M 0 1; 0, M 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ce₂, Matrix.mul_apply]

private theorem cx_pre0 : modePrefix cxP₁ ((0 : Fin 2) : ℕ) = 1 := by simp

private theorem cx_pre1 : modePrefix cxP₁ ((1 : Fin 2) : ℕ) = leftProj ce₁ := by
  simp [modePrefix, cxP₁, List.ofFn_succ]

private theorem cx_prod : modeProd cxP₁ = leftProj ce₁ * rightProj ce₂ := by
  simp [modeProd, cxP₁, List.ofFn_succ]

private theorem cx_field0 (t : ℝ) : cxQ₀ 0 (modePrefix cxP₁ ((0 : Fin 2) : ℕ) (cxAdot t)) =
    (-Real.sin t) • !![(0 : ℝ), 0; 1, 0] := by
  have hQ0 : cxQ₀ 0 = rightProj ce₁ := rfl
  rw [cx_pre0, hQ0, one_apply_eq_self, rightProj_ce₁]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]

private theorem cx_field1 (t : ℝ) : cxQ₀ 1 (modePrefix cxP₁ ((1 : Fin 2) : ℕ) (cxAdot t)) = 0 := by
  have hQ1 : cxQ₀ 1 = leftProj ce₁ := rfl
  rw [cx_pre1, hQ1, leftProj_ce₁, leftProj_ce₁]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]

private theorem cx_sfield0 (t : ℝ) :
    cxP₁ 0 (cxQ₀ 0 (modePrefix cxP₁ ((0 : Fin 2) : ℕ) (cxAdot t))) = 0 := by
  have hP0 : cxP₁ 0 = leftProj ce₁ := rfl
  rw [cx_field0, hP0, leftProj_ce₁]
  ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem cx_sfield1 (t : ℝ) :
    cxP₁ 1 (cxQ₀ 1 (modePrefix cxP₁ ((1 : Fin 2) : ℕ) (cxAdot t))) = 0 := by
  rw [cx_field1, map_zero]

private theorem cx_cfield (t : ℝ) : modeProd cxP₁ (cxAdot t) = 0 := by
  rw [cx_prod]
  change leftProj ce₁ (rightProj ce₂ (cxAdot t)) = 0
  rw [rightProj_ce₂, leftProj_ce₁]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]

/-- OP-TN-05 (source: arXiv 1709.02594, Thm 3 statement vs. proof), counterexample: the
statement of LVW18 Thm 3, which assumes `Wᵢ(t₁)ᵀWᵢ(t₀)` invertible only for the modes `i ≥ 2`, is
false.  For `A(t) = e₂ v(t)ᵀ` on `[0, π/2]` the column space is constant (`W₂ ≡ e₂`, the mode-2
condition holds), the row spaces at `0` and `π/2` are orthogonal (`A(π/2)` is not recoverable from
its mode-`0` `K`-step projection `A(π/2) e₁e₁ᵀ = 0`), nested Tucker KSL steps with exact
`K`-steps exist for the bases `cxP₁`, and every such step misses `A(π/2)`. -/
theorem tucker_ksl_not_exact :
    IsDerivRHS (fun t _ => cxAdot t) cxA 0 (Real.pi / 2) ∧
    (∀ t, ce₂ * (ce₂ᵀ * cxA t) = cxA t) ∧
    ¬ Exactness.IsRecoverable Exactness.leftMulClass (rightProj ce₁) (cxA (Real.pi / 2)) ∧
    (∃ (X : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (K : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (YS : Fin 2 → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (YC : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      IsTuckerKSLStep (fun t _ => cxAdot t) 1 cxQ₀ cxP₁ 0 (Real.pi / 2) (cxA 0) X K YS YC ∧
      IsExactKSteps (fun t _ => cxAdot t) cxQ₀ cxP₁ 0 (Real.pi / 2) X K) ∧
    ∀ (X : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ) (K : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (YS : Fin 2 → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (YC : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      IsTuckerKSLStep (fun t _ => cxAdot t) 1 cxQ₀ cxP₁ 0 (Real.pi / 2) (cxA 0) X K YS YC →
      IsExactKSteps (fun t _ => cxAdot t) cxQ₀ cxP₁ 0 (Real.pi / 2) X K →
      YC (Real.pi / 2) ≠ cxA (Real.pi / 2) := by
  refine ⟨cx_isDerivRHS, cx_colspace, cx_not_recoverable, ?_, ?_⟩
  · refine ⟨![cxA 0, 0, 0], fun _ => 0, fun _ _ => 0, fun _ => 0, ?_, ?_⟩
    · have h1 : ce₁ᵀ * ce₁ = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
        ext i j; fin_cases i; fin_cases j; simp [ce₁, Matrix.mul_apply]
      have h2 : ce₂ᵀ * ce₂ = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
        ext i j; fin_cases i; fin_cases j; simp [ce₂, Matrix.mul_apply]
      refine ⟨fun i => ?_, fun i => ?_, fun i j x => ?_, rfl, fun i => ?_, fun i => ?_,
        fun i t ht => ?_, fun i => ?_, fun i => rfl, fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact isOrthProj_rightProj h1
        · exact isOrthProj_leftProj h1
      · fin_cases i
        · exact isOrthProj_leftProj h1
        · exact isOrthProj_rightProj h2
      · fin_cases i <;> fin_cases j
        · rfl
        · exact leftProj_rightProj_comm _ _ _
        · exact (leftProj_rightProj_comm _ _ _).symm
        · rfl
      · fin_cases i
        · change rightProj ce₁ (cxA 0) = cxA 0
          rw [rightProj_ce₁]; ext i j; fin_cases i <;> fin_cases j <;> simp [cxA]
        · exact map_zero _
      · exact map_zero _
      · fin_cases i
        · have e : (1 - cxP₁ 0) ((1 - cxQ₀ 0) (modePrefix cxP₁ ((0 : Fin 2) : ℕ) (cxAdot t))) =
              !![(0 : ℝ), 0; 0, Real.cos t] := by
            have hP0 : cxP₁ 0 = leftProj ce₁ := rfl
            have hQ0 : cxQ₀ 0 = rightProj ce₁ := rfl
            rw [cx_pre0, hP0, hQ0]
            simp only [sub_apply, one_apply_eq_self,
              leftProj_ce₁, rightProj_ce₁]
            ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]
          change ‖(1 - cxP₁ 0) ((1 - cxQ₀ 0) (modePrefix cxP₁ ((0 : Fin 2) : ℕ) (cxAdot t)))‖ ≤ 1
          rw [e, Frobenius.norm_def]
          apply Real.sqrt_le_one.2
          simpa [Fin.sum_univ_two] using Real.abs_cos_le_one t
        · have e : (1 - cxP₁ 1) ((1 - cxQ₀ 1) (modePrefix cxP₁ ((1 : Fin 2) : ℕ) (cxAdot t))) =
              0 := by
            have hP1 : cxP₁ 1 = rightProj ce₂ := rfl
            have hQ1 : cxQ₀ 1 = leftProj ce₁ := rfl
            rw [cx_pre1, hP1, hQ1]
            simp only [sub_apply, one_apply_eq_self,
              leftProj_ce₁, rightProj_ce₂]
            ext i j; fin_cases i <;> fin_cases j <;> simp [cxAdot]
          change ‖(1 - cxP₁ 1) ((1 - cxQ₀ 1) (modePrefix cxP₁ ((1 : Fin 2) : ℕ) (cxAdot t)))‖ ≤ 1
          rw [e, norm_zero]; exact zero_le_one
      · refine cx_odeSolution_zero (fun t => ?_) _ _
        fin_cases i
        · exact neg_eq_zero.2 (cx_sfield0 t)
        · exact neg_eq_zero.2 (cx_sfield1 t)
      · fin_cases i <;> rfl
      · exact cx_odeSolution_zero (fun t => cx_cfield t) _ _
      · rfl
    · intro i
      fin_cases i
      · refine ⟨fun t => Real.cos t • !![(0 : ℝ), 0; 1, 0], ⟨?_, fun t _ => ?_⟩, ?_, ?_⟩
        · exact (Real.continuous_cos.smul continuous_const).continuousOn
        · have h := ((Real.hasDerivAt_cos t).smul_const !![(0 : ℝ), 0; 1, 0]).hasDerivWithinAt
            (s := Set.Ici t)
          have e : kslModeField cxQ₀ cxP₁ (fun t _ => cxAdot t) ((0 : Fin 2))
              t (Real.cos t • !![(0 : ℝ), 0; 1, 0]) = (-Real.sin t) • !![(0 : ℝ), 0; 1, 0] :=
            cx_field0 t
          change HasDerivWithinAt _ (kslModeField cxQ₀ cxP₁ (fun t _ => cxAdot t) ((0 : Fin 2))
            t (Real.cos t • !![(0 : ℝ), 0; 1, 0])) _ _
          rw [e]; exact h
        · ext i j; fin_cases i <;> fin_cases j <;> simp [cxA]
        · ext i j; fin_cases i <;> fin_cases j <;> simp
      · refine ⟨fun _ => 0, cx_odeSolution_zero (fun t => ?_) _ _, rfl, rfl⟩
        exact cx_field1 t
  · intro X K YS YC hs hK
    obtain ⟨hKe, hXe, hYe⟩ := tucker_ksl_explicit (by positivity) cx_isDerivRHS hs hK
    have h0 := hs.start
    have hΔ : cxA (Real.pi / 2) - cxA 0 = !![(0 : ℝ), 0; -1, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [cxA]
    have hK0 : K 0 = X 0 + rightProj ce₁ (cxA (Real.pi / 2) - cxA 0) := by
      have := hKe 0
      simpa [modePrefix, cxQ₀] using this
    have hX0 : X 1 = K 0 + -(leftProj ce₁ (rightProj ce₁ (cxA (Real.pi / 2) - cxA 0))) := by
      have := hXe 0
      simpa [modePrefix, cxQ₀, cxP₁] using this
    have hK1 : K 1 = X 1 + leftProj ce₁ (leftProj ce₁ (cxA (Real.pi / 2) - cxA 0)) := by
      have := hKe 1
      simpa [modePrefix, cxQ₀, cxP₁, List.ofFn_succ] using this
    have hX1 : X 2 = K 1 + -(rightProj ce₂ (leftProj ce₁ (leftProj ce₁
        (cxA (Real.pi / 2) - cxA 0)))) := by
      have := hXe 1
      simpa [modePrefix, cxQ₀, cxP₁, List.ofFn_succ] using this
    have hY : YC (Real.pi / 2) =
        X 2 + leftProj ce₁ (rightProj ce₂ (cxA (Real.pi / 2) - cxA 0)) := by
      have := hYe
      simpa [modeProd, cxP₁, List.ofFn_succ] using this
    rw [hΔ] at hK0 hX0 hK1 hX1 hY
    have e1 : K 0 = 0 := by
      rw [hK0, h0, rightProj_ce₁]; ext i j; fin_cases i <;> fin_cases j <;> simp [cxA]
    have e2 : X 1 = 0 := by
      rw [hX0, e1, rightProj_ce₁, leftProj_ce₁]; ext i j; fin_cases i <;> fin_cases j <;> simp
    have e3 : K 1 = 0 := by
      rw [hK1, e2, leftProj_ce₁, leftProj_ce₁]; ext i j; fin_cases i <;> fin_cases j <;> simp
    have e4 : X 2 = 0 := by
      rw [hX1, e3, leftProj_ce₁, leftProj_ce₁, rightProj_ce₂]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    intro hEq
    rw [hY, e4, rightProj_ce₂, leftProj_ce₁] at hEq
    have := congrFun (congrFun hEq 1) 1
    simp [cxA] at this

end Counterexample

section Augmented

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Augmented

section CME

open scoped Matrix LeanDLRA.Frobenius

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end CME

end LeanDLRA.OpenProblems.TensorNetworks

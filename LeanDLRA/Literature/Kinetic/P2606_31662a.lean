import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Stability.Conservation

/-!
# Positivity-preserving corrections of low-rank solutions (arXiv 2606.31662)

Kormann, Nazarov, Wen, *Positivity-preserving dynamical low-rank methods for the Vlasov equation*.
This module proves the theorems of Sections 3 and 4 of the paper in the paper's own discrete
setting, on matrices `X ∈ ℝ^{N_x × r}`, `V ∈ ℝ^{N_v × r}`, `K̃`, `S̃`.  This is not a reduction:
both corrections are post-processing steps on these matrices, and the Vlasov equation enters only
through the data.

For the correction PP-KL it proves row separability of (3.3) (`prop_3_1`, `isRowMin_iff_isQPMin`,
`existsUnique_isKMin`, `isRowMin_iff_eq_zero_of_nonneg`), (3.1), (3.2) (`eq_3_1`, `eq_3_2`) and
well-posedness (`pp_kl`).  For the standard QP (3.6) it proves that the KKT conditions are necessary
and sufficient (`isQPMin_iff_exists_kkt`, through an elementary Farkas lemma `farkas_alternative`)
and that the least-norm problem has exactly one solution when feasible (`existsUnique_isQPMin_two`).
For active sets it proves Proposition 3.2 with the corrected closed form (`prop_3_2`,
`row_closed_form`), the failure of the printed form (`printed_formula_3_7_wrong`,
`printed_formula_3_7_false`), the need for non-degeneracy (`nondegeneracy_needed`), a version
without it (`exists_active_subset`, `exists_independent_support`), the stopping test of the
active-set iteration (`isQPMin_of_certificate`), the form with equalities (`active_set_eq`) and the
cost count (`row_active_sets_cost`).  For the correction MMC-PP-S it proves Proposition 4.1
(`prop_4_1`), the reformulation (4.5) as a QP (`mmc_vec_reformulation`), the main statement that a
feasible (4.4) has exactly one solution, which is nonnegative and conserves mass and momentum
exactly (`mmc_pp_s`, `sFeasible_iff_corrected`), closeness to the uncorrected state
(`mmc_pp_s_closest`), KKT conditions and active sets of (4.5) (`mmc_kkt_active_set`), monotonicity
of feasibility under the rank increase of Algorithm 4.1 (`sFeasible_mono`), and instances
(`mmc_pp_s_instance`, `mmc_active_set_instance`).

## Differences from the paper

* **The primal formula in (3.7) is false as printed.**  With the paper's `A = -V`, `y = bᵢᵀ`, the
  multiplier `μ* = -2 (A_S A_Sᵀ)⁻¹ y_S` is right, but `δK* = ½ A_Sᵀ μ* = -A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` has
  the wrong sign.  It contradicts `x* = -½ Aᵀ λ` in the paper's own proof of Proposition 3.2.  The
  correct formula is `δK* = -½ A_Sᵀ μ* = A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S = -V_Sᵀ (V_S V_Sᵀ)⁻¹ b_S`.  The
  printed point is the negative of the minimiser, and it is infeasible whenever the correction is
  nonzero.
* "Non-degeneracy" in Proposition 3.2 is not defined in the paper.  It is formalised as LICQ on the
  active set, following the paper's proof.  The bound `|S| ≤ r` is then a dimension count, also for
  "strictly active" constraints (`λⱼ > 0`).
* Proposition 3.2 is printed for the general QP (3.6).  Its proof uses `x⋆ = -½ Aᵀ λ`, which is
  stationarity for `Q = 2 I`, `c = 0`, `A_eq = 0`, and `prop_3_2` is stated in that setting, the
  one of (3.4).  The KKT conditions themselves are proved for general `Q ⪰ 0`, `c` and `A_eq`
  (`isQPMin_iff_exists_kkt`).
* Existence and uniqueness of the minimisers, and necessity of the KKT conditions, are not stated in
  the paper.  They are proved here, without constraint qualification.
* The costs `O(N_x r³)` and `O(r⁶)` are operation counts.  What is proved is their mathematical
  content, the sizes of the linear systems: `∑ |Sᵢ|³ ≤ N_x r³` and `|S| + 2 ≤ r²`, under LICQ.  The
  number of active-set iterations is not bounded here, and not in the paper.  The active-set
  iteration itself is not formalised, only its stopping test.
* Remark 3.4 says that solvability of (3.3), (3.5) is not guaranteed, but `δK = -K̃` is always
  feasible, so that they are always uniquely solvable (`pp_kl`, already the library's
  `ppKL_feasible_unique`). The concern is valid for `F ⪰ ε 1` of Remark 3.3, which `KFeasible`
  covers, and for (4.4).
* The L-problem (3.5) is not stated separately: it is (3.3) with `X` in the role of `V`.
* As in the paper's matrix formulas, the momentum uses one velocity component `v`, and the constant
  `(Δx)^d (Δv)^d` is dropped.  The time integrator (Algorithm 2.1) is not used: the theorems hold
  for all `X`, `V`, `K̃`, `S̃`, and orthonormality is assumed only where it is stated.
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix Kronecker LeanDLRA.Frobenius

namespace LeanDLRA.Literature.P2606_31662

open Matrix

/-! ### Farkas' alternative -/

section Farkas

variable {ι n : Type*} [Fintype n]

/-- **Farkas' alternative**, the tool for the KKT conditions before Proposition 3.2 of arXiv
2606.31662, for finitely many vectors of `ℝⁿ`, by the elementary induction on the number of
generators: `z` is a nonnegative combination of the `a j`, `j ∈ s`, or some `d` has `a j ⬝ᵥ d ≤ 0`
for all `j ∈ s` and `0 < z ⬝ᵥ d`. Tool for `IsQPMin.exists_kkt`. -/
theorem farkas_alternative (s : Finset ι) :
    ∀ (a : ι → n → ℝ) (z : n → ℝ),
      (∃ l : ι → ℝ, (∀ j, 0 ≤ l j) ∧ z = ∑ j ∈ s, l j • a j) ∨
        ∃ d : n → ℝ, (∀ j ∈ s, a j ⬝ᵥ d ≤ 0) ∧ 0 < z ⬝ᵥ d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a z
    by_cases hz : z = 0
    · exact Or.inl ⟨0, by simp, by simp [hz]⟩
    · refine Or.inr ⟨z, by simp, ?_⟩
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (fun h => hz (dotProduct_self_eq_zero.1 h.symm))
  | insert j0 s hj0 ih =>
    intro a z
    have hne : ∀ j ∈ s, j ≠ j0 := fun j hj h => hj0 (h ▸ hj)
    rcases ih a z with ⟨l, hl, hz⟩ | ⟨d, hd, hzd⟩
    · refine Or.inl ⟨Function.update l j0 0, fun j => ?_, ?_⟩
      · by_cases h : j = j0
        · simp [h]
        · simpa [Function.update_of_ne h] using hl j
      · rw [Finset.sum_insert hj0, hz]
        simp only [Function.update_self, zero_smul, zero_add]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
    · by_cases had : a j0 ⬝ᵥ d ≤ 0
      · refine Or.inr ⟨d, fun j hj => ?_, hzd⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact had
        · exact hd j hj
      · have hp : 0 < a j0 ⬝ᵥ d := not_le.1 had
        have hp0 : a j0 ⬝ᵥ d ≠ 0 := hp.ne'
        rcases ih (fun j => a j - (a j ⬝ᵥ d / (a j0 ⬝ᵥ d)) • a j0)
            (z - (z ⬝ᵥ d / (a j0 ⬝ᵥ d)) • a j0) with
          ⟨l, hl, hz'⟩ | ⟨d', hd', hzd'⟩
        · set p := a j0 ⬝ᵥ d with hpdef
          refine Or.inl ⟨Function.update l j0
            (z ⬝ᵥ d / p - ∑ j ∈ s, l j * (a j ⬝ᵥ d / p)), fun j => ?_, ?_⟩
          · by_cases h : j = j0
            · subst h
              simp only [Function.update_self]
              have h1 : ∑ j ∈ s, l j * (a j ⬝ᵥ d / p) ≤ 0 :=
                Finset.sum_nonpos fun j hj => mul_nonpos_of_nonneg_of_nonpos (hl j)
                  (div_nonpos_of_nonpos_of_nonneg (hd j hj) hp.le)
              have h2 : 0 ≤ z ⬝ᵥ d / p := div_nonneg hzd.le hp.le
              linarith
            · simpa [Function.update_of_ne h] using hl j
          · rw [Finset.sum_insert hj0]
            simp only [Function.update_self]
            have h1 : ∑ j ∈ s, Function.update l j0
                (z ⬝ᵥ d / p - ∑ j ∈ s, l j * (a j ⬝ᵥ d / p)) j • a j = ∑ j ∈ s, l j • a j :=
              Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
            rw [h1]
            have h3 : ∑ j ∈ s, l j • (a j - (a j ⬝ᵥ d / p) • a j0)
                = ∑ j ∈ s, l j • a j - (∑ j ∈ s, l j * (a j ⬝ᵥ d / p)) • a j0 := by
              rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [smul_sub, smul_smul]
            have h2 : z = (∑ j ∈ s, l j • a j - (∑ j ∈ s, l j * (a j ⬝ᵥ d / p)) • a j0)
                + (z ⬝ᵥ d / p) • a j0 := by
              rw [← h3, ← hz']; abel
            rw [sub_smul]
            nth_rewrite 1 [h2]
            abel
        · have hdot : ∀ w : n → ℝ, w ⬝ᵥ (d' - (a j0 ⬝ᵥ d' / (a j0 ⬝ᵥ d)) • d)
              = (w - (w ⬝ᵥ d / (a j0 ⬝ᵥ d)) • a j0) ⬝ᵥ d' := by
            intro w
            rw [dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul,
              smul_eq_mul]
            ring
          refine Or.inr ⟨d' - (a j0 ⬝ᵥ d' / (a j0 ⬝ᵥ d)) • d, fun j hj => ?_, ?_⟩
          · rw [hdot]
            rcases Finset.mem_insert.1 hj with rfl | hj
            · rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, div_self hp0, one_mul, sub_self]
            · exact hd' j hj
          · rw [hdot]
            exact hzd'

/-- `farkas_alternative` with a multiplier that is supported in `s`, summed over all indices (tool
for the KKT conditions of arXiv 2606.31662). -/
theorem farkas_alternative' [Fintype ι] (s : Finset ι) (a : ι → n → ℝ) (z : n → ℝ) :
    (∃ l : ι → ℝ, (∀ j, 0 ≤ l j) ∧ (∀ j, j ∉ s → l j = 0) ∧ z = ∑ j, l j • a j) ∨
      ∃ d : n → ℝ, (∀ j ∈ s, a j ⬝ᵥ d ≤ 0) ∧ 0 < z ⬝ᵥ d := by
  classical
  rcases farkas_alternative s a z with ⟨l, hl, hz⟩ | h
  · refine Or.inl ⟨fun j => if j ∈ s then l j else 0, fun j => ?_, fun j hj => by simp [hj], ?_⟩
    · dsimp only
      split_ifs
      · exact hl j
      · exact le_rfl
    · rw [hz]
      simp only [ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
  · exact Or.inr h

end Farkas

/-! ### The standard quadratic program (3.6) and its KKT conditions -/

section QP

variable {ι κ n : Type*} [Fintype n]

/-- The objective `½ xᵀ Q x + cᵀ x` of the standard QP (3.6) of arXiv 2606.31662. -/
noncomputable def qpObj (Q : Matrix n n ℝ) (c x : n → ℝ) : ℝ :=
  (1 / 2) * (x ⬝ᵥ Q *ᵥ x) + c ⬝ᵥ x

/-- The constraints `A x ≤ y`, `A_eq x = y_eq` of the standard QP (3.6) of arXiv 2606.31662. -/
def QPFeasible (A : Matrix ι n ℝ) (y : ι → ℝ) (Aeq : Matrix κ n ℝ) (yeq : κ → ℝ)
    (x : n → ℝ) : Prop :=
  (∀ j, (A *ᵥ x) j ≤ y j) ∧ Aeq *ᵥ x = yeq

/-- `x` is a global minimiser of the standard QP (3.6) of arXiv 2606.31662. -/
def IsQPMin (Q : Matrix n n ℝ) (c : n → ℝ) (A : Matrix ι n ℝ) (y : ι → ℝ) (Aeq : Matrix κ n ℝ)
    (yeq : κ → ℝ) (x : n → ℝ) : Prop :=
  QPFeasible A y Aeq yeq x ∧ ∀ w, QPFeasible A y Aeq yeq w → qpObj Q c x ≤ qpObj Q c w

/-- The KKT conditions of (3.6) in arXiv 2606.31662. The paper displays them for `c = 0` and `A_eq =
0`; here `c` and the multiplier `nu` of the equality constraints are kept, which is needed for
(4.5). -/
structure IsKKT [Fintype ι] [Fintype κ] (Q : Matrix n n ℝ) (c : n → ℝ) (A : Matrix ι n ℝ)
    (y : ι → ℝ) (Aeq : Matrix κ n ℝ) (yeq : κ → ℝ) (x : n → ℝ) (lam : ι → ℝ) (nu : κ → ℝ) :
    Prop where
  /-- Stationarity. -/
  stat : Q *ᵥ x + c + Aᵀ *ᵥ lam + Aeqᵀ *ᵥ nu = 0
  /-- Primal feasibility. -/
  primal : QPFeasible A y Aeq yeq x
  /-- Dual feasibility. -/
  dual : ∀ j, 0 ≤ lam j
  /-- Complementarity. -/
  compl : lam ⬝ᵥ (A *ᵥ x - y) = 0

/-- Expansion of the objective of (3.6) around `x`, for symmetric `Q`. -/
lemma qpObj_add_sub {Q : Matrix n n ℝ} (hQ : Qᵀ = Q) (c x d : n → ℝ) :
    qpObj Q c (x + d) - qpObj Q c x
      = (1 / 2) * (d ⬝ᵥ Q *ᵥ d) + (Q *ᵥ x + c) ⬝ᵥ d := by
  have hs : d ⬝ᵥ Q *ᵥ x = x ⬝ᵥ Q *ᵥ d := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  simp only [qpObj, mulVec_add, add_dotProduct, dotProduct_add, hs]
  rw [dotProduct_comm (Q *ᵥ x) d, hs]
  ring

/-- Sufficiency of the KKT conditions for the convex QP (3.6) of arXiv 2606.31662. -/
theorem IsKKT.isQPMin [Fintype ι] [Fintype κ] {Q : Matrix n n ℝ} {c : n → ℝ} {A : Matrix ι n ℝ}
    {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ} {lam : ι → ℝ} {nu : κ → ℝ}
    (hQ : Q.PosSemidef) (h : IsKKT Q c A y Aeq yeq x lam nu) : IsQPMin Q c A y Aeq yeq x := by
  refine ⟨h.primal, fun w hw => ?_⟩
  have hsym : Qᵀ = Q := by simpa using hQ.isHermitian.eq
  have h1 := qpObj_add_sub hsym c x (w - x)
  rw [add_sub_cancel] at h1
  have hg : Q *ᵥ x + c = -(Aᵀ *ᵥ lam) - Aeqᵀ *ᵥ nu := by
    have := h.stat
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero]
    rw [← this]; abel
  have h2 : (Aᵀ *ᵥ lam) ⬝ᵥ (w - x) = lam ⬝ᵥ (A *ᵥ (w - x)) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  have h3 : (Aeqᵀ *ᵥ nu) ⬝ᵥ (w - x) = nu ⬝ᵥ (Aeq *ᵥ (w - x)) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  have h4 : Aeq *ᵥ (w - x) = 0 := by
    rw [mulVec_sub, hw.2, h.primal.2, sub_self]
  have h5 : lam ⬝ᵥ (A *ᵥ (w - x)) = lam ⬝ᵥ (A *ᵥ w - y) := by
    have := h.compl
    rw [dotProduct_sub] at this
    rw [mulVec_sub, dotProduct_sub, dotProduct_sub]
    linarith
  have h6 : lam ⬝ᵥ (A *ᵥ w - y) ≤ 0 :=
    Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (h.dual j) (sub_nonpos.2 (hw.1 j))
  have h7 : 0 ≤ (w - x) ⬝ᵥ Q *ᵥ (w - x) := by
    simpa using hQ.dotProduct_mulVec_nonneg (w - x)
  have h8 : (Q *ᵥ x + c) ⬝ᵥ (w - x) = -(lam ⬝ᵥ (A *ᵥ w - y)) := by
    rw [hg, sub_dotProduct, neg_dotProduct, h2, h3, h4, dotProduct_zero, h5, sub_zero]
  linarith

/-- Necessity of the KKT conditions for the QP (3.6) of arXiv 2606.31662. For linear constraints no
constraint qualification is needed: the proof is `farkas_alternative'` applied to the active
constraints and the equalities. -/
theorem IsQPMin.exists_kkt [Fintype ι] [Fintype κ] {Q : Matrix n n ℝ} {c : n → ℝ}
    {A : Matrix ι n ℝ} {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ}
    (hQ : Q.PosSemidef) (hx : IsQPMin Q c A y Aeq yeq x) :
    ∃ lam nu, IsKKT Q c A y Aeq yeq x lam nu := by
  classical
  obtain ⟨hf, hmin⟩ := hx
  have hsym : Qᵀ = Q := by simpa using hQ.isHermitian.eq
  let T : Finset (ι ⊕ (κ ⊕ κ)) :=
    Finset.univ.filter fun p => Sum.elim (fun j => (A *ᵥ x) j = y j) (fun _ => True) p
  let a : ι ⊕ (κ ⊕ κ) → n → ℝ :=
    Sum.elim (fun j => A j) (Sum.elim (fun k => Aeq k) (fun k => -Aeq k))
  rcases farkas_alternative' T a (-(Q *ᵥ x + c)) with ⟨l, hl, hsupp, hz⟩ | ⟨d, hd, hgd⟩
  · refine ⟨fun j => l (Sum.inl j), fun k => l (Sum.inr (Sum.inl k)) - l (Sum.inr (Sum.inr k)),
      ?_, hf, fun j => hl _, ?_⟩
    · have h1 : -(Q *ᵥ x + c) = ∑ j, l (Sum.inl j) • A j
          + ∑ k, (l (Sum.inr (Sum.inl k)) - l (Sum.inr (Sum.inr k))) • Aeq k := by
        rw [hz, Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [a, Sum.elim_inl, Sum.elim_inr, sub_smul, smul_neg, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib]
        abel
      rw [mulVec_transpose, mulVec_transpose, vecMul_eq_sum, vecMul_eq_sum]
      rw [add_assoc, ← h1]
      abel
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (A *ᵥ x) j = y j
      · simp [hj]
      · have h0 : l (Sum.inl j) = 0 := hsupp (Sum.inl j) (by simpa [T] using hj)
        simp [h0]
  · exfalso
    have hdA : ∀ j, (A *ᵥ x) j = y j → (A *ᵥ d) j ≤ 0 := fun j hj =>
      hd (Sum.inl j) (by simpa [T] using hj)
    have hdE : Aeq *ᵥ d = 0 := by
      funext k
      have h1 : (Aeq *ᵥ d) k ≤ 0 := hd (Sum.inr (Sum.inl k)) (by simp [T])
      have h2 : (-Aeq k) ⬝ᵥ d ≤ 0 := hd (Sum.inr (Sum.inr k)) (by simp [T])
      rw [neg_dotProduct] at h2
      exact le_antisymm h1 (by simpa [mulVec] using h2)
    have hg : (Q *ᵥ x + c) ⬝ᵥ d < 0 := by
      rw [neg_dotProduct] at hgd
      linarith
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
    have hfeas : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j, (A *ᵥ x) j + t * (A *ᵥ d) j ≤ y j := by
      refine Filter.eventually_all.2 fun j => ?_
      by_cases hj : (A *ᵥ x) j = y j
      · filter_upwards [hpos] with t ht
        have := mul_nonpos_of_nonneg_of_nonpos ht.le (hdA j hj)
        linarith
      · have hlt : (A *ᵥ x) j < y j := lt_of_le_of_ne (hf.1 j) hj
        have hc : Continuous fun t : ℝ => (A *ᵥ x) j + t * (A *ᵥ d) j := by fun_prop
        have h0 : ∀ᶠ t : ℝ in 𝓝 0, (A *ᵥ x) j + t * (A *ᵥ d) j < y j :=
          hc.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
        exact (h0.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.le
    have hdec : ∀ᶠ t : ℝ in 𝓝[>] 0,
        (Q *ᵥ x + c) ⬝ᵥ d + (1 / 2) * t * (d ⬝ᵥ Q *ᵥ d) < 0 := by
      have hc : Continuous fun t : ℝ => (Q *ᵥ x + c) ⬝ᵥ d + (1 / 2) * t * (d ⬝ᵥ Q *ᵥ d) := by
        fun_prop
      have h0 : ∀ᶠ t : ℝ in 𝓝 0, (Q *ᵥ x + c) ⬝ᵥ d + (1 / 2) * t * (d ⬝ᵥ Q *ᵥ d) < 0 :=
        hc.continuousAt.eventually_lt continuousAt_const (by simpa using hg)
      exact h0.filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ht, ht1, ht2⟩ := (hpos.and (hfeas.and hdec)).exists
    have hw : QPFeasible A y Aeq yeq (x + t • d) := by
      refine ⟨fun j => ?_, ?_⟩
      · have := ht1 j
        simpa [mulVec_add, mulVec_smul] using this
      · rw [mulVec_add, mulVec_smul, hdE, hf.2]
        simp
    have h1 := hmin _ hw
    have h2 := qpObj_add_sub hsym c x (t • d)
    have h3 : (1 / 2 : ℝ) * ((t • d) ⬝ᵥ Q *ᵥ (t • d)) + (Q *ᵥ x + c) ⬝ᵥ (t • d)
        = t * ((Q *ᵥ x + c) ⬝ᵥ d + (1 / 2) * t * (d ⬝ᵥ Q *ᵥ d)) := by
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [h3] at h2
    have h4 := mul_neg_of_pos_of_neg ht ht2
    linarith

/-- **KKT conditions of the standard QP** (arXiv 2606.31662, (3.6) and the display before
Proposition 3.2): for `Q` positive semidefinite, `x` is a global minimiser iff it satisfies the KKT
conditions. The paper states the conditions without proof, for `c = 0` and `A_eq = 0`; here `c` and
the equality constraints are kept, and no constraint qualification is needed. -/
theorem isQPMin_iff_exists_kkt [Fintype ι] [Fintype κ] {Q : Matrix n n ℝ} {c : n → ℝ}
    {A : Matrix ι n ℝ} {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ}
    (hQ : Q.PosSemidef) :
    IsQPMin Q c A y Aeq yeq x ↔ ∃ lam nu, IsKKT Q c A y Aeq yeq x lam nu :=
  ⟨IsQPMin.exists_kkt hQ, fun ⟨_, _, h⟩ => h.isQPMin hQ⟩

/-- The Euclidean norm `‖w‖₂` of a coordinate vector, which is not the norm on `n → ℝ`. -/
noncomputable def l2 {n : Type*} [Fintype n] (w : n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 w : EuclideanSpace ℝ n)‖

/-- `‖w‖₂² = w ⬝ᵥ w`. -/
lemma l2_sq (w : n → ℝ) : l2 w ^ 2 = w ⬝ᵥ w := by
  rw [l2, EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

/-- `‖w‖₂ ≥ 0`. -/
lemma l2_nonneg (w : n → ℝ) : 0 ≤ l2 w := norm_nonneg _

/-- Comparing Euclidean norms is comparing `w ⬝ᵥ w`. -/
lemma l2_le_l2_iff {w w' : n → ℝ} : l2 w ≤ l2 w' ↔ w ⬝ᵥ w ≤ w' ⬝ᵥ w' := by
  rw [← l2_sq, ← l2_sq]
  exact (sq_le_sq₀ (l2_nonneg _) (l2_nonneg _)).symm

omit [Fintype n] in
/-- `Q = 2 I` is positive semidefinite, so that (3.4) is a convex QP. -/
lemma posSemidef_two_smul_one [DecidableEq n] : ((2 : ℝ) • (1 : Matrix n n ℝ)).PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one (by norm_num)

/-- For `Q = 2 I`, `c = 0` the objective of (3.6) is `‖x‖₂²`. -/
lemma qpObj_two_smul_one [DecidableEq n] (x : n → ℝ) :
    qpObj ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 x = x ⬝ᵥ x := by
  simp only [qpObj, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, zero_dotProduct,
    add_zero]
  ring

/-- For `Q = 2 I`, `c = 0` the QP (3.6) minimises `‖x‖₂`, as stated after (3.6) in the paper. -/
lemma isQPMin_two_iff [DecidableEq n] {A : Matrix ι n ℝ} {y : ι → ℝ} {Aeq : Matrix κ n ℝ}
    {yeq : κ → ℝ} {x : n → ℝ} :
    IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y Aeq yeq x ↔
      QPFeasible A y Aeq yeq x ∧ ∀ w, QPFeasible A y Aeq yeq w → l2 x ≤ l2 w := by
  simp only [IsQPMin, qpObj_two_smul_one, l2_le_l2_iff]

/-- The feasible set of (3.6) is convex. -/
lemma QPFeasible.combo {A : Matrix ι n ℝ} {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ}
    {x w : n → ℝ} (hx : QPFeasible A y Aeq yeq x) (hw : QPFeasible A y Aeq yeq w) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : QPFeasible A y Aeq yeq (a • x + b • w) := by
  refine ⟨fun j => ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (hx.1 j) ha
    have h2 := mul_le_mul_of_nonneg_left (hw.1 j) hb
    have h3 : a * y j + b * y j = y j := by rw [← add_mul, hab, one_mul]
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hx.2, hw.2, ← add_smul, hab, one_smul]

/-- Entries of `B x` are continuous on Euclidean space. -/
lemma continuous_mulVec_ofLp {τ : Type*} (B : Matrix τ n ℝ) (k : τ) :
    Continuous fun u : EuclideanSpace ℝ n => (B *ᵥ WithLp.ofLp u) k := by
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _))

/-- **Existence and uniqueness for `Q = 2 I`, `c = 0`**: if the constraints of (3.6) are feasible,
the least-norm problem has exactly one minimiser. This is what makes "the" correction of arXiv
2606.31662, (3.4) and (4.5), well defined. The paper takes it for granted. -/
theorem existsUnique_isQPMin_two [DecidableEq n] {A : Matrix ι n ℝ} {y : ι → ℝ}
    {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ}
    (h : ∃ w, QPFeasible A y Aeq yeq w) :
    ∃! x, IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y Aeq yeq x := by
  obtain ⟨w₀, hw₀⟩ := h
  let K : Set (EuclideanSpace ℝ n) := {u | QPFeasible A y Aeq yeq (WithLp.ofLp u)}
  have hne : K.Nonempty := ⟨WithLp.toLp 2 w₀, hw₀⟩
  have hconv : Convex ℝ K := fun u hu v hv a b ha hb hab => hu.combo hv ha hb hab
  have hcl : IsClosed K := by
    have : K = (⋂ j, {u | (A *ᵥ WithLp.ofLp u) j ≤ y j}) ∩ {u | Aeq *ᵥ WithLp.ofLp u = yeq} := by
      ext u
      simp [K, QPFeasible]
    rw [this]
    exact IsClosed.inter
      (isClosed_iInter fun j => isClosed_le (continuous_mulVec_ofLp A j) continuous_const)
      (isClosed_eq (continuous_pi fun k => continuous_mulVec_ofLp Aeq k) continuous_const)
  obtain ⟨u, hu, hvi⟩ := exists_metricProj hne hcl.isComplete hconv 0
  have hmin : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y Aeq yeq (WithLp.ofLp u) := by
    refine isQPMin_two_iff.2 ⟨hu, fun w hw => ?_⟩
    have := (norm_sub_le_of_metricProj hvi (a := WithLp.toLp 2 w) hw).2
    simpa [l2] using this
  refine ⟨_, hmin, fun x' hx' => ?_⟩
  obtain ⟨hf', hm'⟩ := isQPMin_two_iff.1 hx'
  obtain ⟨hf, hm⟩ := isQPMin_two_iff.1 hmin
  have hmid := hf'.combo hf (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have h1 := l2_le_l2_iff.1 (hm' _ hmid)
  have h2 := l2_le_l2_iff.1 (hm _ hmid)
  have h5 : (x' - WithLp.ofLp u) ⬝ᵥ (x' - WithLp.ofLp u) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul,
      sub_dotProduct, dotProduct_sub] at h1 h2 ⊢
    rw [dotProduct_comm (WithLp.ofLp u) x'] at *
    linarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h5)

end QP

/-! ### Proposition 3.1: row separability -/

section RowSeparability

variable {nx nv r : Type*} [Fintype r]

/-- The constraint of (3.3) in arXiv 2606.31662: `-δK Vᵀ ⪯ b` entrywise. The paper has `b = K̃ Vᵀ`;
a general `b` also covers `F ⪰ ε 1` of Remark 3.3, with `b = K̃ Vᵀ - ε 1`. -/
def KFeasible (V : Matrix nv r ℝ) (b : Matrix nx nv ℝ) (dK : Matrix nx r ℝ) : Prop :=
  ∀ i j, (-(dK * Vᵀ)) i j ≤ b i j

/-- `δK` solves (3.3) of arXiv 2606.31662: it is feasible and minimises the Frobenius norm. -/
def IsKMin [Fintype nx] (V : Matrix nv r ℝ) (b : Matrix nx nv ℝ) (dK : Matrix nx r ℝ) : Prop :=
  KFeasible V b dK ∧ ∀ dK', KFeasible V b dK' → ‖dK‖ ≤ ‖dK'‖

/-- The constraint of the row problem (3.4) of arXiv 2606.31662: `-V w ≤ bᵢᵀ`. -/
def RowFeasible (V : Matrix nv r ℝ) (bi : nv → ℝ) (w : r → ℝ) : Prop :=
  ∀ j, -(V *ᵥ w) j ≤ bi j

/-- `w = (δKᵢ)ᵀ` solves the row problem (3.4) of arXiv 2606.31662. -/
def IsRowMin (V : Matrix nv r ℝ) (bi : nv → ℝ) (w : r → ℝ) : Prop :=
  RowFeasible V bi w ∧ ∀ w', RowFeasible V bi w' → l2 w ≤ l2 w'

/-- The entries of `δK Vᵀ` are those of `V (δKᵢ)ᵀ`. -/
lemma mul_transpose_apply (dK : Matrix nx r ℝ) (V : Matrix nv r ℝ) (i : nx) (j : nv) :
    (dK * Vᵀ) i j = (V *ᵥ dK i) j := by
  simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]

/-- The constraints of (3.3) are those of (3.4) row by row. -/
lemma kFeasible_iff {V : Matrix nv r ℝ} {b : Matrix nx nv ℝ} {dK : Matrix nx r ℝ} :
    KFeasible V b dK ↔ ∀ i, RowFeasible V (b i) (dK i) := by
  simp only [KFeasible, RowFeasible, Matrix.neg_apply, mul_transpose_apply]

/-- The squared Frobenius norm is the sum of the squared Euclidean norms of the rows. -/
lemma norm_sq_eq_sum_l2 [Fintype nx] (dK : Matrix nx r ℝ) : ‖dK‖ ^ 2 = ∑ i, l2 (dK i) ^ 2 := by
  rw [Frobenius.norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [l2_sq]
  simp [dotProduct, sq]

/-- **Proposition 3.1 (row separability)** (arXiv 2606.31662, label "Proposition 3.1: row
separability"). Problem (3.3), `min ‖δK‖_F` subject to `-δK Vᵀ ⪯ b`, is equivalent to the `N_x`
independent problems (3.4), `min ‖δKᵢ‖₂` subject to `-V (δKᵢ)ᵀ ≤ bᵢᵀ`: the constraints of (3.3) are
those of (3.4) row by row, `‖δK‖_F² = ∑ ‖δKᵢ‖₂²`, and `δK` solves (3.3) iff every row solves (3.4).
The paper has `b = K̃ Vᵀ`; here `b` is arbitrary, so that the constraint `F ⪰ ε 1` of Remark 3.3 is
included. The cost `O(N_x r³)` of the header is treated in `row_active_sets_cost`. -/
theorem prop_3_1 [Fintype nx] (V : Matrix nv r ℝ) (b : Matrix nx nv ℝ) (dK : Matrix nx r ℝ) :
    (KFeasible V b dK ↔ ∀ i, RowFeasible V (b i) (dK i)) ∧
      ‖dK‖ ^ 2 = ∑ i, l2 (dK i) ^ 2 ∧
      (IsKMin V b dK ↔ ∀ i, IsRowMin V (b i) (dK i)) := by
  classical
  refine ⟨kFeasible_iff, norm_sq_eq_sum_l2 dK, ⟨fun ⟨hf, hmin⟩ i => ?_, fun h => ?_⟩⟩
  · refine ⟨kFeasible_iff.1 hf i, fun w hw => ?_⟩
    have hf' : KFeasible V b (dK.updateRow i w) := by
      refine kFeasible_iff.2 fun i' => ?_
      by_cases hi : i' = i
      · subst hi
        simpa [Matrix.updateRow_self] using hw
      · simpa [Matrix.updateRow_ne hi] using kFeasible_iff.1 hf i'
    have h1 := hmin _ hf'
    have h2 : ‖dK‖ ^ 2 ≤ ‖dK.updateRow i w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [norm_sq_eq_sum_l2, norm_sq_eq_sum_l2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase (a := i) _ (fun i' => l2 (dK.updateRow i w i') ^ 2)
        (Finset.mem_univ i)] at h2
    have h3 : ∑ i' ∈ Finset.univ.erase i, l2 (dK.updateRow i w i') ^ 2
        = ∑ i' ∈ Finset.univ.erase i, l2 (dK i') ^ 2 :=
      Finset.sum_congr rfl fun i' hi' => by
        rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hi')]
    rw [h3, Matrix.updateRow_self] at h2
    exact (sq_le_sq₀ (l2_nonneg _) (l2_nonneg _)).1 (by linarith)
  · refine ⟨kFeasible_iff.2 fun i => (h i).1, fun dK' hf' => ?_⟩
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_sq_eq_sum_l2, norm_sq_eq_sum_l2]
    exact Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (l2_nonneg _) ((h i).2 _ (kFeasible_iff.1 hf' i)) 2

/-- The row problem (3.4) is the standard QP (3.6) with `c = 0`, `Q = 2 I_r`, `A = -V`, `A_eq = 0`,
`y_eq = 0`, `y = bᵢᵀ`, as stated in Section 3.2 of arXiv 2606.31662. -/
theorem isRowMin_iff_isQPMin {κ : Type*} [DecidableEq r] {V : Matrix nv r ℝ} {bi : nv → ℝ}
    {w : r → ℝ} :
    IsRowMin V bi w ↔
      IsQPMin ((2 : ℝ) • (1 : Matrix r r ℝ)) 0 (-V) bi (0 : Matrix κ r ℝ) 0 w := by
  have hf : ∀ w, RowFeasible V bi w ↔ QPFeasible (-V) bi (0 : Matrix κ r ℝ) 0 w := by
    intro w
    simp [RowFeasible, QPFeasible, neg_mulVec]
  rw [isQPMin_two_iff]
  simp only [IsRowMin, hf]

/-- The first step of the workflow after (3.7) in arXiv 2606.31662: if `bᵢ ≥ 0` then `δKᵢ = 0`, and
this is the only solution of (3.4). -/
theorem isRowMin_iff_eq_zero_of_nonneg {V : Matrix nv r ℝ} {bi : nv → ℝ} (hb : ∀ j, 0 ≤ bi j)
    {w : r → ℝ} : IsRowMin V bi w ↔ w = 0 := by
  have h0 : RowFeasible V bi 0 := fun j => by simpa using hb j
  have hl0 : l2 (0 : r → ℝ) = 0 := by simp [l2]
  constructor
  · intro hw
    have h1 := hw.2 0 h0
    rw [hl0] at h1
    have h2 : l2 w ^ 2 = 0 := by nlinarith [l2_nonneg w]
    rw [l2_sq] at h2
    exact dotProduct_self_eq_zero.1 h2
  · rintro rfl
    exact ⟨h0, fun w' _ => by rw [hl0]; exact l2_nonneg _⟩

/-- **Solving (3.3) is solving (3.4)**, the existence part of Proposition 3.1 of arXiv 2606.31662:
if every row problem (3.4) is feasible, then (3.3) has exactly one solution, and it is assembled
from the unique row solutions. For `b = K̃ Vᵀ` feasibility always holds (`w = -K̃ᵢ`), see `pp_kl`.
-/
theorem existsUnique_isKMin [Fintype nx] {V : Matrix nv r ℝ} {b : Matrix nx nv ℝ}
    (h : ∀ i, ∃ w, RowFeasible V (b i) w) : ∃! dK, IsKMin V b dK := by
  classical
  have hrow : ∀ i, ∃! w, IsRowMin V (b i) w := by
    intro i
    have h1 : ∃ w, QPFeasible (-V) (b i) (0 : Matrix Empty r ℝ) 0 w := by
      obtain ⟨w, hw⟩ := h i
      exact ⟨w, by simpa [RowFeasible, QPFeasible, neg_mulVec] using hw⟩
    simpa only [← isRowMin_iff_isQPMin] using existsUnique_isQPMin_two h1
  choose dK hdK hdKu using hrow
  refine ⟨Matrix.of dK, (prop_3_1 V b _).2.2.2 fun i => hdK i, fun dK' h' => ?_⟩
  funext i
  exact hdKu i _ ((prop_3_1 V b _).2.2.1 h' i)

end RowSeparability

/-! ### Proposition 3.2: active sets and the closed form (3.7) -/

section ActiveSet

variable {ι κ n : Type*} [Fintype n]

/-- The (weakly) active set `{j | (A x)ⱼ = yⱼ}` of a point `x` for the constraints `A x ≤ y`. -/
noncomputable def activeSet [Fintype ι] (A : Matrix ι n ℝ) (y : ι → ℝ) (x : n → ℝ) : Finset ι :=
  Finset.univ.filter fun j => (A *ᵥ x) j = y j

/-- The sub-matrix `A_S` of the rows in `S`. -/
abbrev rowsOf (A : Matrix ι n ℝ) (S : Finset ι) : Matrix S n ℝ := A.submatrix (↑) id

/-- The non-degeneracy condition of Proposition 3.2 (LICQ): the rows of `A` in `S` are linearly
independent. -/
def IsLICQ (A : Matrix ι n ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ fun j : S => A j

/-- The multiplier `μ* = -2 (A_S A_Sᵀ)⁻¹ y_S` of (3.7) in arXiv 2606.31662. -/
noncomputable def muStar [DecidableEq ι] (A : Matrix ι n ℝ) (y : ι → ℝ) (S : Finset ι) : S → ℝ :=
  (-2 : ℝ) • ((rowsOf A S * (rowsOf A S)ᵀ)⁻¹ *ᵥ fun j : S => y j)

/-- The primal solution `A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S`, with the correct sign. -/
noncomputable def xStar [DecidableEq ι] (A : Matrix ι n ℝ) (y : ι → ℝ) (S : Finset ι) : n → ℝ :=
  (rowsOf A S)ᵀ *ᵥ ((rowsOf A S * (rowsOf A S)ᵀ)⁻¹ *ᵥ fun j : S => y j)

/-- The primal formula `-A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` as printed in (3.7) of arXiv 2606.31662. -/
noncomputable def printedDeltaK [DecidableEq ι] (A : Matrix ι n ℝ) (y : ι → ℝ) (S : Finset ι) :
    n → ℝ :=
  -(rowsOf A S)ᵀ *ᵥ ((rowsOf A S * (rowsOf A S)ᵀ)⁻¹ *ᵥ fun j : S => y j)

/-- If `B` has independent rows, `B Bᵀ` is invertible. -/
lemma isUnit_mul_transpose {σ : Type*} [Fintype σ] [DecidableEq σ] {B : Matrix σ n ℝ}
    (hB : LinearIndependent ℝ fun j => B j) : IsUnit (B * Bᵀ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro g g' hgg
  have h0 : (B * Bᵀ) *ᵥ (g - g') = 0 := by
    rw [mulVec_sub, sub_eq_zero]
    exact hgg
  have h1 : (Bᵀ *ᵥ (g - g')) ⬝ᵥ (Bᵀ *ᵥ (g - g')) = 0 := by
    have h5 : (Bᵀ *ᵥ (g - g')) ⬝ᵥ (Bᵀ *ᵥ (g - g')) = (g - g') ⬝ᵥ ((B * Bᵀ) *ᵥ (g - g')) := by
      rw [← mulVec_mulVec, dotProduct_mulVec (g - g') B, mulVec_transpose]
    rw [h5, h0, dotProduct_zero]
  have h2 := dotProduct_self_eq_zero.1 h1
  rw [mulVec_transpose, vecMul_eq_sum] at h2
  have h3 := Fintype.linearIndependent_iff.1 hB (g - g') h2
  funext j
  exact sub_eq_zero.1 (h3 j)

/-- The computation behind (3.7) of arXiv 2606.31662: if `x = Bᵀ m` lies in the row space of `B`,
which has independent rows, and `B x = z`, then `m` and `x` are given by the normal equations. -/
theorem closed_form_of_rowSpace {σ : Type*} [Fintype σ] [DecidableEq σ] {B : Matrix σ n ℝ}
    (hB : LinearIndependent ℝ fun j => B j) {z : σ → ℝ} {x : n → ℝ} {m : σ → ℝ}
    (h1 : B *ᵥ x = z) (h2 : x = Bᵀ *ᵥ m) :
    m = (B * Bᵀ)⁻¹ *ᵥ z ∧ x = Bᵀ *ᵥ ((B * Bᵀ)⁻¹ *ᵥ z) := by
  have hU := isUnit_mul_transpose hB
  have h3 : (B * Bᵀ) *ᵥ m = z := by rw [← mulVec_mulVec, ← h2, h1]
  have h4 : m = (B * Bᵀ)⁻¹ *ᵥ z := by
    rw [← h3, mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
      one_mulVec]
  exact ⟨h4, h4 ▸ h2⟩

/-- A KKT multiplier vanishes on inactive constraints. -/
lemma IsKKT.lam_eq_zero [Fintype ι] [Fintype κ] {Q : Matrix n n ℝ} {c : n → ℝ} {A : Matrix ι n ℝ}
    {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ} {lam : ι → ℝ} {nu : κ → ℝ}
    (h : IsKKT Q c A y Aeq yeq x lam nu) {j : ι} (hj : (A *ᵥ x) j ≠ y j) : lam j = 0 := by
  have h1 := h.compl
  have h2 : ∀ j ∈ (Finset.univ : Finset ι), lam j * (A *ᵥ x - y) j ≤ 0 := fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (h.dual j) (sub_nonpos.2 (h.primal.1 j))
  have h3 := (Finset.sum_eq_zero_iff_of_nonpos h2).1 h1 j (Finset.mem_univ j)
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact h4
  · exact absurd (sub_eq_zero.1 h4) hj

omit [Fintype n] in
/-- If `lam` is supported in `S`, then `Aᵀ lam = A_Sᵀ lam_S`. -/
lemma transpose_mulVec_of_support [Fintype ι] {A : Matrix ι n ℝ} {S : Finset ι}
    {lam : ι → ℝ} (h : ∀ j, j ∉ S → lam j = 0) :
    Aᵀ *ᵥ lam = (rowsOf A S)ᵀ *ᵥ fun j : S => lam j := by
  classical
  rw [mulVec_transpose, mulVec_transpose, vecMul_eq_sum, vecMul_eq_sum]
  have h1 : ∑ j : S, (fun j : S => lam j) j • rowsOf A S j = ∑ j ∈ S, lam j • A j :=
    Finset.sum_coe_sort S fun j => lam j • A j
  rw [h1]
  exact (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by simp [h j hj]).symm

/-- For `Q = 2 I`, `c = 0`, stationarity expresses `x` through the rows carrying the multiplier. -/
lemma IsKKT.eq_neg_half [Fintype ι] [Fintype κ] [DecidableEq n] {A : Matrix ι n ℝ} {y : ι → ℝ}
    {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ} {lam : ι → ℝ} {nu : κ → ℝ}
    (h : IsKKT ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y Aeq yeq x lam nu) :
    x = (-(1 / 2) : ℝ) • (Aᵀ *ᵥ lam + Aeqᵀ *ᵥ nu) := by
  have h1 := h.stat
  simp only [smul_mulVec, one_mulVec, add_zero] at h1
  have h2 : Aᵀ *ᵥ lam + Aeqᵀ *ᵥ nu = -((2 : ℝ) • x) := by
    rw [eq_neg_iff_add_eq_zero, ← h1]
    abel
  rw [h2, smul_neg, smul_smul]
  have h3 : (-(1 / 2) : ℝ) * 2 = -1 := by norm_num
  rw [h3, neg_smul, one_smul, neg_neg]

/-- The closed form behind (3.7) of arXiv 2606.31662, for any index set `S` that carries the
multiplier, consists of active constraints and has independent rows. -/
theorem IsKKT.closed_form [Fintype ι] [DecidableEq ι] [DecidableEq n] {A : Matrix ι n ℝ}
    {y : ι → ℝ} {x : n → ℝ} {lam : ι → ℝ} {nu : Empty → ℝ}
    (h : IsKKT ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x lam nu)
    {S : Finset ι} (hS : IsLICQ A S) (hact : ∀ j ∈ S, (A *ᵥ x) j = y j)
    (hsupp : ∀ j, j ∉ S → lam j = 0) :
    (∀ j : S, lam j = muStar A y S j) ∧ x = xStar A y S := by
  have h1 : rowsOf A S *ᵥ x = fun j : S => y j := by
    funext j
    exact hact j j.2
  have h2 : x = (rowsOf A S)ᵀ *ᵥ ((-(1 / 2) : ℝ) • fun j : S => lam j) := by
    conv_lhs => rw [h.eq_neg_half]
    rw [transpose_mulVec_of_support hsupp, mulVec_smul]
    simp
  obtain ⟨h3, h4⟩ := closed_form_of_rowSpace (B := rowsOf A S) hS h1 h2
  refine ⟨fun j => ?_, h4⟩
  have h5 := congrFun h3 j
  simp only [Pi.smul_apply, smul_eq_mul] at h5
  simp only [muStar, Pi.smul_apply, smul_eq_mul]
  linarith

/-- The relation `-½ A_Sᵀ μ* = A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S`, with the sign of the proof of Proposition
3.2. -/
lemma neg_half_mu_eq_xStar [DecidableEq ι] (A : Matrix ι n ℝ) (y : ι → ℝ) (S : Finset ι) :
    (-(1 / 2) : ℝ) • ((rowsOf A S)ᵀ *ᵥ muStar A y S) = xStar A y S := by
  rw [xStar, muStar, mulVec_smul, smul_smul]
  norm_num

/-- **Proposition 3.2 and the closed form (3.7), corrected** (arXiv 2606.31662, label "Proposition
3.2: active-set closed form"). Let `x` be the minimiser of (3.6) with `Q = 2 I`, `c = 0`, `A_eq =
0`, and suppose LICQ holds on the active set `S`. Then at most `r` constraints are active, any KKT
multiplier has at most `r` positive entries (the paper's "strictly active"), `A_S A_Sᵀ` is
invertible, the multiplier `μ* = -2 (A_S A_Sᵀ)⁻¹ y_S` of (3.7) is nonnegative, and `x = -½
A_Sᵀ μ* = A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S`.

The paper states the proposition for (3.6) with general `Q`, `c`, `A_eq`; its proof, and this
theorem, take `Q = 2 I`, `c = 0`, `A_eq = 0` (the row problem (3.4)).
The paper prints `δK* = ½ A_Sᵀ μ* = -A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S`, which has the wrong sign: see
`printed_formula_3_7_false`. The paper's "non-degeneracy" is formalised as LICQ, following its
proof, and without it the claim fails (`nondegeneracy_needed`), although a variant survives
(`exists_active_subset`). The closed form applies to the smaller set `{j | λⱼ > 0}` as well, when
this is the set one wants to use: see `IsKKT.closed_form`. -/
theorem prop_3_2 [Fintype ι] [DecidableEq ι] [DecidableEq n] {A : Matrix ι n ℝ}
    {y : ι → ℝ} {x : n → ℝ}
    (hx : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x)
    (hS : IsLICQ A (activeSet A y x)) :
    (activeSet A y x).card ≤ Fintype.card n ∧
      (∀ (lam : ι → ℝ) (nu : Empty → ℝ),
        IsKKT ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x lam nu →
          (Finset.univ.filter fun j => 0 < lam j).card ≤ Fintype.card n) ∧
      IsUnit (rowsOf A (activeSet A y x) * (rowsOf A (activeSet A y x))ᵀ) ∧
      (∀ j, 0 ≤ muStar A y (activeSet A y x) j) ∧
      x = (-(1 / 2) : ℝ) • ((rowsOf A (activeSet A y x))ᵀ *ᵥ muStar A y (activeSet A y x)) ∧
      x = xStar A y (activeSet A y x) := by
  obtain ⟨lam, nu, hK⟩ := hx.exists_kkt posSemidef_two_smul_one
  have hact : ∀ j ∈ activeSet A y x, (A *ᵥ x) j = y j := fun j hj => (Finset.mem_filter.1 hj).2
  have hsupp : ∀ j, j ∉ activeSet A y x → lam j = 0 := fun j hj =>
    hK.lam_eq_zero fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
  obtain ⟨h1, h2⟩ := hK.closed_form hS hact hsupp
  have hcard : (activeSet A y x).card ≤ Fintype.card n := by
    simpa using hS.fintype_card_le_finrank
  refine ⟨hcard, fun lam' nu' hK' => ?_, isUnit_mul_transpose hS, fun j => ?_, ?_, h2⟩
  · refine (Finset.card_le_card fun j hj => ?_).trans hcard
    by_contra hna
    have hl := hK'.lam_eq_zero (j := j) fun h =>
      hna (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
    have := (Finset.mem_filter.1 hj).2
    linarith
  · rw [← h1 j]
    exact hK.dual j
  · exact h2.trans (neg_half_mu_eq_xStar A y _).symm

omit [Fintype n] in
/-- **Conic Carathéodory reduction**, the tool for `exists_active_subset` (arXiv 2606.31662,
Proposition 3.2 without non-degeneracy): a nonnegative combination can be rewritten as a nonnegative
combination, with support contained in the old one, whose generators are linearly independent. -/
theorem exists_independent_support [Fintype ι] (a : ι → n → ℝ) (z : n → ℝ) :
    ∀ (N : ℕ) (l : ι → ℝ), (Finset.univ.filter fun j => l j ≠ 0).card ≤ N → (∀ j, 0 ≤ l j) →
      z = ∑ j, l j • a j →
      ∃ l' : ι → ℝ, (∀ j, 0 ≤ l' j) ∧ z = ∑ j, l' j • a j ∧ (∀ j, l' j ≠ 0 → l j ≠ 0) ∧
        LinearIndependent ℝ fun j : (Finset.univ.filter fun j => l' j ≠ 0 : Finset ι) => a j := by
  classical
  intro N
  induction N with
  | zero =>
    intro l hN hl hz
    have h0 : ∀ j, l j = 0 := fun j => by
      by_contra hj
      have : j ∈ (Finset.univ.filter fun j => l j ≠ 0) := by simp [hj]
      simp only [Nat.le_zero, Finset.card_eq_zero] at hN
      simp [hN] at this
    refine ⟨l, hl, hz, fun j h => h, ?_⟩
    have he : (Finset.univ.filter fun j => l j ≠ 0) = ∅ := by
      simp [h0]
    rw [he]
    exact linearIndependent_empty_type
  | succ N ih =>
    intro l hN hl hz
    set S : Finset ι := Finset.univ.filter fun j => l j ≠ 0 with hS
    by_cases hind : LinearIndependent ℝ fun j : S => a j
    · exact ⟨l, hl, hz, fun j h => h, hind⟩
    obtain ⟨g₀, hg₀, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.1 hind
    obtain ⟨g, hg, j₁, hj₁⟩ : ∃ g : S → ℝ, ∑ j, g j • a j = 0 ∧ ∃ j, 0 < g j := by
      rcases lt_or_gt_of_ne hj₀ with h | h
      · refine ⟨-g₀, ?_, j₀, by simpa using h⟩
        simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hg₀, neg_zero]
      · exact ⟨g₀, hg₀, j₀, h⟩
    obtain ⟨j₂, hj₂, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun j => 0 < g j)
      (fun j : S => l j / g j) ⟨j₁, by simpa using hj₁⟩
    have hj₂pos : 0 < g j₂ := (Finset.mem_filter.1 hj₂).2
    set t : ℝ := l j₂ / g j₂ with ht
    have hlpos : ∀ j : S, 0 < l j := fun j =>
      lt_of_le_of_ne (hl j) (Ne.symm (Finset.mem_filter.1 j.2).2)
    have htpos : 0 < t := div_pos (hlpos j₂) hj₂pos
    let G : ι → ℝ := fun j => if h : j ∈ S then g ⟨j, h⟩ else 0
    have hG : ∀ j : S, G j = g j := fun j => by simp [G]
    have hG0 : ∀ j, j ∉ S → G j = 0 := fun j hj => by simp [G, hj]
    have hsum : ∑ j, G j • a j = 0 := by
      have h1 : ∑ j ∈ S, G j • a j = ∑ j : S, g j • a j := by
        rw [← Finset.sum_coe_sort S]
        exact Finset.sum_congr rfl fun j _ => by rw [hG]
      rw [← hg, ← h1]
      exact (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => by simp [hG0 j hj]).symm
    have hl' : ∀ j, 0 ≤ l j - t * G j := by
      intro j
      by_cases hj : j ∈ S
      · have h2 := hG ⟨j, hj⟩
        simp only at h2
        rw [h2]
        by_cases hgj : 0 < g ⟨j, hj⟩
        · have h3 := hmin ⟨j, hj⟩ (by simpa using hgj)
          simp only at h3
          rw [le_div_iff₀ hgj] at h3
          linarith
        · have h3 := mul_nonneg htpos.le (sub_nonneg.2 (not_lt.1 hgj))
          have := hl j
          linarith
      · rw [hG0 j hj, mul_zero, sub_zero]
        exact hl j
    have hz' : z = ∑ j, (l j - t * G j) • a j := by
      have h1 : ∑ j, (l j - t * G j) • a j = ∑ j, l j • a j - t • ∑ j, G j • a j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [sub_smul, mul_smul]
      rw [h1, hsum, smul_zero, sub_zero, hz]
    have hsub : ∀ j, l j - t * G j ≠ 0 → l j ≠ 0 := by
      intro j hj hlj
      have hjS : j ∉ S := fun h => (Finset.mem_filter.1 h).2 hlj
      exact hj (by rw [hG0 j hjS, hlj]; ring)
    have hj₂0 : l j₂ - t * G j₂ = 0 := by
      rw [hG, ht]
      field_simp
      ring
    have hcard : (Finset.univ.filter fun j => l j - t * G j ≠ 0).card ≤ N := by
      have h1 : (Finset.univ.filter fun j => l j - t * G j ≠ 0) ⊂ S := by
        refine ⟨fun j hj => ?_, fun h => ?_⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hsub j (Finset.mem_filter.1 hj).2⟩
        · exact (Finset.mem_filter.1 (h j₂.2)).2 hj₂0
      have h2 := Finset.card_lt_card h1
      omega
    obtain ⟨l', h1, h2, h3, h4⟩ := ih _ hcard hl' hz'
    exact ⟨l', h1, h2, fun j hj => hsub j (h3 j hj), h4⟩

/-- **Active-set sparsity without non-degeneracy** (arXiv 2606.31662, Proposition 3.2 and (3.7),
strengthened). For the minimiser `x` of (3.6) with `Q = 2 I`, `c = 0`, `A_eq = 0`, there is always a
set `S` of active constraints with independent rows, hence `|S| ≤ r`, for which the multiplier `μ*`
of (3.7) is nonnegative and `x = A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` (the corrected sign, see
`printed_formula_3_7_false`). The paper assumes non-degeneracy; here the conclusion is for a
suitable subset of the active set, as `nondegeneracy_needed` shows it must be. -/
theorem exists_active_subset [Fintype ι] [DecidableEq ι] [DecidableEq n]
    {A : Matrix ι n ℝ} {y : ι → ℝ} {x : n → ℝ}
    (hx : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x) :
    ∃ S ⊆ activeSet A y x, IsLICQ A S ∧ S.card ≤ Fintype.card n ∧
      (∀ j, 0 ≤ muStar A y S j) ∧ x = xStar A y S := by
  obtain ⟨lam, nu, hK⟩ := hx.exists_kkt posSemidef_two_smul_one
  have h0 : (-(2 : ℝ)) • x = ∑ j, lam j • A j := by
    have h1 := hK.eq_neg_half
    simp only [transpose_zero, zero_mulVec, add_zero] at h1
    rw [mulVec_transpose, vecMul_eq_sum] at h1
    conv_lhs => rw [h1]
    rw [smul_smul]
    norm_num
  obtain ⟨l', hl', hz, hsupp, hind⟩ :=
    exists_independent_support (fun j => A j) _ _ lam le_rfl hK.dual h0
  have hzero : ∀ j, (A *ᵥ x) j ≠ y j → l' j = 0 := fun j hj => by
    by_contra h
    exact hsupp j h (hK.lam_eq_zero hj)
  have hK' : IsKKT ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x l' nu := by
    refine ⟨?_, hK.primal, hl', ?_⟩
    · simp only [transpose_zero, zero_mulVec, add_zero, smul_mulVec, one_mulVec]
      rw [mulVec_transpose, vecMul_eq_sum, ← hz, neg_smul, add_neg_cancel]
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (A *ᵥ x) j = y j
      · simp [hj]
      · simp [hzero j hj]
  set S : Finset ι := Finset.univ.filter fun j => l' j ≠ 0 with hS
  have hact : ∀ j ∈ S, (A *ᵥ x) j = y j := fun j hj => by
    by_contra h
    exact (Finset.mem_filter.1 hj).2 (hzero j h)
  have hsupp' : ∀ j, j ∉ S → l' j = 0 := fun j hj => by
    by_contra h
    exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
  obtain ⟨h1, h2⟩ := hK'.closed_form hind hact hsupp'
  refine ⟨S, fun j hj => Finset.mem_filter.2 ⟨Finset.mem_univ j, hact j hj⟩, hind, ?_, ?_, h2⟩
  · simpa using LinearIndependent.fintype_card_le_finrank hind
  · intro j
    rw [← h1 j]
    exact hl' j

/-- `xStar` solves the active constraints of `S`, when `A_S` has independent rows. -/
lemma rowsOf_mulVec_xStar [DecidableEq ι] {A : Matrix ι n ℝ} {S : Finset ι} (hS : IsLICQ A S)
    (y : ι → ℝ) : rowsOf A S *ᵥ xStar A y S = fun j : S => y j := by
  have hU := isUnit_mul_transpose (B := rowsOf A S) hS
  rw [xStar, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), one_mulVec]

/-- **Termination certificate of the active-set iteration** (arXiv 2606.31662, the use of (3.7) in
the workflow of Section 3.2). If `A_S` has independent rows, `μ* ≥ 0` and the corrected closed form
`A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` is feasible, then it is the minimiser of (3.6) with `Q = 2 I`, `c = 0`,
`A_eq = 0`. The paper states this implicitly and with the wrong sign, see
`printed_formula_3_7_wrong`. -/
theorem isQPMin_of_certificate [Finite ι] [DecidableEq ι] [DecidableEq n]
    {A : Matrix ι n ℝ} {y : ι → ℝ} {S : Finset ι} (hS : IsLICQ A S)
    (hμ : ∀ j, 0 ≤ muStar A y S j) (hf : ∀ j, (A *ᵥ xStar A y S) j ≤ y j) :
    IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 (xStar A y S) := by
  cases nonempty_fintype ι
  let lam : ι → ℝ := fun j => if h : j ∈ S then muStar A y S ⟨j, h⟩ else 0
  have hlam : ∀ j : S, lam j = muStar A y S j := fun j => by simp [lam]
  have hlam0 : ∀ j, j ∉ S → lam j = 0 := fun j hj => by simp [lam, hj]
  have hact : ∀ j ∈ S, (A *ᵥ xStar A y S) j = y j := fun j hj =>
    congrFun (rowsOf_mulVec_xStar hS y) ⟨j, hj⟩
  have hK : IsKKT ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 (xStar A y S)
      lam 0 := by
    refine ⟨?_, ⟨hf, by simp⟩, fun j => ?_, ?_⟩
    · have h1 : (fun j : S => lam j) = muStar A y S := funext hlam
      rw [transpose_mulVec_of_support hlam0, h1]
      simp only [transpose_zero, zero_mulVec, add_zero, smul_mulVec, one_mulVec]
      rw [← neg_half_mu_eq_xStar, smul_smul]
      norm_num
    · by_cases hj : j ∈ S
      · rw [hlam ⟨j, hj⟩]
        exact hμ _
      · rw [hlam0 j hj]
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j ∈ S
      · simp [hact j hj]
      · simp [hlam0 j hj]
  exact hK.isQPMin posSemidef_two_smul_one

/-- **The primal formula of (3.7) has the wrong sign** (arXiv 2606.31662, label "Proposition 3.2:
active-set closed form": the claim `δK* = -A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` is false). Under the hypotheses of
`prop_3_2`, the printed `δK* = ½ A_Sᵀ μ* = -A_Sᵀ (A_S A_Sᵀ)⁻¹ y_S` equals `-x`, not `x`. The
multiplier `μ*` is printed correctly, and the correct relation is `x = -½ A_Sᵀ μ*`, as in the proof
of Proposition 3.2. If the correction is nonzero the printed point differs from the minimiser and is
not even feasible, and on the active set `A_S` maps it to `-y_S` instead of `y_S`. A concrete
instance is `printed_formula_3_7_false`. -/
theorem printed_formula_3_7_wrong [Fintype ι] [DecidableEq ι] [DecidableEq n]
    {A : Matrix ι n ℝ} {y : ι → ℝ} {x : n → ℝ}
    (hx : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 x)
    (hS : IsLICQ A (activeSet A y x)) :
    printedDeltaK A y (activeSet A y x)
        = (1 / 2 : ℝ) • ((rowsOf A (activeSet A y x))ᵀ *ᵥ muStar A y (activeSet A y x)) ∧
      printedDeltaK A y (activeSet A y x) = -x ∧
      rowsOf A (activeSet A y x) *ᵥ printedDeltaK A y (activeSet A y x)
        = -(fun j : activeSet A y x => y j) ∧
      (x ≠ 0 → printedDeltaK A y (activeSet A y x) ≠ x ∧
        ¬ QPFeasible A y (0 : Matrix Empty n ℝ) 0 (printedDeltaK A y (activeSet A y x))) := by
  obtain ⟨-, -, -, -, -, h2⟩ := prop_3_2 hx hS
  have h3 : printedDeltaK A y (activeSet A y x) = -xStar A y (activeSet A y x) := by
    rw [printedDeltaK, xStar, neg_mulVec]
  have h4 : printedDeltaK A y (activeSet A y x) = -x := by
    rw [h3, ← h2]
  refine ⟨?_, h4, ?_, fun h0 => ⟨?_, fun hf => ?_⟩⟩
  · rw [printedDeltaK, muStar, mulVec_smul, smul_smul, neg_mulVec]
    norm_num
  · rw [h3, mulVec_neg, rowsOf_mulVec_xStar hS]
  · rw [h4]
    intro h5
    apply h0
    have h6 : x + x = 0 := by
      nth_rewrite 2 [← h5]
      simp
    funext i
    have h7 := congrFun h6 i
    simp only [Pi.add_apply, Pi.zero_apply] at h7 ⊢
    linarith
  · rw [h4] at hf
    obtain ⟨hf0, hm⟩ := isQPMin_two_iff.1 hx
    have hmin' : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y (0 : Matrix Empty n ℝ) 0 (-x) := by
      refine isQPMin_two_iff.2 ⟨hf, fun w hw => ?_⟩
      have h5 := l2_le_l2_iff.1 (hm w hw)
      refine l2_le_l2_iff.2 ?_
      simpa using h5
    obtain ⟨z, -, hz⟩ := existsUnique_isQPMin_two (A := A) (y := y) (Aeq := (0 : Matrix Empty n ℝ))
      (yeq := 0) ⟨x, hf0⟩
    have h5 : x = -x := (hz x hx).trans (hz _ hmin').symm
    apply h0
    funext i
    have h7 := congrFun h5 i
    simp only [Pi.neg_apply, Pi.zero_apply] at h7 ⊢
    linarith

/-- **A concrete failure of the printed primal formula of (3.7)** (arXiv 2606.31662). Take `N_x =
N_v = r = 1`, `V = 1` (orthonormal), `K̃ = -1`, so that `F̃ = -1`. The solution of (3.3)/(3.4) is
`δK = 1`, with `F = 0`, and the constraint `-V δK ≤ b` is active with independent rows. But the
printed formula gives `δK* = -1`, which violates the constraint and gives `F = -2`: it doubles the
negative value that it should remove. -/
theorem printed_formula_3_7_false :
    ∃ (V Kt : Matrix (Fin 1) (Fin 1) ℝ) (x : Fin 1 → ℝ),
      Vᵀ * V = 1 ∧ IsRowMin V ((Kt * Vᵀ) 0) x ∧
      IsLICQ (-V) (activeSet (-V) ((Kt * Vᵀ) 0) x) ∧
      x ≠ printedDeltaK (-V) ((Kt * Vᵀ) 0) (activeSet (-V) ((Kt * Vᵀ) 0) x) ∧
      ¬ RowFeasible V ((Kt * Vᵀ) 0) (printedDeltaK (-V) ((Kt * Vᵀ) 0)
        (activeSet (-V) ((Kt * Vᵀ) 0) x)) ∧
      ((Kt + (Matrix.of fun _ => printedDeltaK (-V) ((Kt * Vᵀ) 0)
        (activeSet (-V) ((Kt * Vᵀ) 0) x) : Matrix (Fin 1) (Fin 1) ℝ)) * Vᵀ :
          Matrix (Fin 1) (Fin 1) ℝ) 0 0 = -2 := by
  have hb : ((-1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) 0
      = fun _ => -1 := by
    funext j
    fin_cases j
    simp
  have hmin : IsRowMin (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => -1) (fun _ => 1) := by
    refine ⟨fun j => by simp, fun w' hw' => l2_le_l2_iff.2 ?_⟩
    have h1 := hw' 0
    simp only [one_mulVec] at h1
    simp only [dotProduct, Fin.sum_univ_one]
    nlinarith
  have hact : activeSet (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => -1) (fun _ => 1) = {0} := by
    ext j
    fin_cases j
    simp [activeSet, neg_mulVec]
  have hS : IsLICQ (-(1 : Matrix (Fin 1) (Fin 1) ℝ))
      (activeSet (-(1 : Matrix (Fin 1) (Fin 1) ℝ)) (fun _ => -1) (fun _ => 1)) := by
    rw [hact]
    have : Unique ↥({0} : Finset (Fin 1)) :=
      ⟨⟨⟨0, Finset.mem_singleton_self 0⟩⟩, fun j => Subtype.ext (Subsingleton.elim _ _)⟩
    refine linearIndependent_unique_iff.2 fun h => ?_
    have h1 := congrFun h 0
    have h2 : ((default : ↥({0} : Finset (Fin 1))) : Fin 1) = 0 := Subsingleton.elim _ _
    simp [h2] at h1
  have hsign := printed_formula_3_7_wrong (isRowMin_iff_isQPMin.1 hmin) hS
  have hne : (fun _ => 1 : Fin 1 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  refine ⟨1, -1, fun _ => 1, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact hmin
  · rw [hb]; exact hS
  · rw [hb]; exact fun h => (hsign.2.2.2 hne).1 h.symm
  · rw [hb]
    intro h
    apply (hsign.2.2.2 hne).2
    exact ⟨fun j => by simpa [neg_mulVec] using h j, by simp⟩
  · rw [hb, hsign.2.1]
    simp [Matrix.mul_apply]
    norm_num

/-- **Non-degeneracy cannot be dropped in Proposition 3.2** (arXiv 2606.31662). For `r = 1` and the
doubled constraint `-x ≤ -1`, `-x ≤ -1`, both constraints are active at the optimum, and both carry
a positive multiplier, so two constraints are (strictly) active in dimension one. -/
theorem nondegeneracy_needed :
    ∃ (A : Matrix (Fin 2) (Fin 1) ℝ) (y : Fin 2 → ℝ) (x : Fin 1 → ℝ) (lam : Fin 2 → ℝ)
      (nu : Empty → ℝ),
      IsKKT ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 A y (0 : Matrix Empty (Fin 1) ℝ) 0 x lam
        nu ∧
      IsQPMin ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 A y (0 : Matrix Empty (Fin 1) ℝ) 0 x ∧
      (∀ j, 0 < lam j) ∧ Fintype.card (Fin 1) < (activeSet A y x).card := by
  have hK : IsKKT ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0
      (!![-1; -1] : Matrix (Fin 2) (Fin 1) ℝ) ![-1, -1] (0 : Matrix Empty (Fin 1) ℝ) 0 ![1] ![1, 1]
      (fun e => e.elim) := by
    refine ⟨?_, ⟨?_, by simp⟩, ?_, ?_⟩
    · funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      norm_num
    · intro j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct]
    · intro j
      fin_cases j <;> simp
    · simp [dotProduct, Fin.sum_univ_two]
  refine ⟨_, _, _, _, _, hK, hK.isQPMin posSemidef_two_smul_one, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp
  · have : activeSet (!![-1; -1] : Matrix (Fin 2) (Fin 1) ℝ) ![-1, -1] ![1] = Finset.univ := by
      ext j
      fin_cases j <;> simp [activeSet, Matrix.mulVec, dotProduct]
    rw [this]
    simp

/-- The closed form (3.7) in terms of `V` and `bᵢ`, for the row problem (3.4) of arXiv 2606.31662:
with `A = -V`, `y = bᵢᵀ`, and LICQ on the active set `S`, `|S| ≤ r` and `(δKᵢ)ᵀ = -V_Sᵀ (V_S V_Sᵀ)⁻¹
b_S`, which is the sign that makes `V_S (δKᵢ)ᵀ = -b_S`. The formula printed in the paper is the
negative of this, see `printed_formula_3_7_wrong`. -/
theorem row_closed_form {nv r : Type*} [Fintype nv] [DecidableEq nv] [Fintype r]
    {V : Matrix nv r ℝ} {bi : nv → ℝ} {w : r → ℝ} (hw : IsRowMin V bi w)
    (hS : IsLICQ V (activeSet (-V) bi w)) :
    (activeSet (-V) bi w).card ≤ Fintype.card r ∧
      w = -((rowsOf V (activeSet (-V) bi w))ᵀ *ᵥ
        ((rowsOf V (activeSet (-V) bi w) * (rowsOf V (activeSet (-V) bi w))ᵀ)⁻¹ *ᵥ
          fun j : activeSet (-V) bi w => bi j)) := by
  classical
  have hS' : IsLICQ (-V) (activeSet (-V) bi w) := by
    have h := hS.units_smul fun _ : activeSet (-V) bi w => (-1 : ℝˣ)
    have he : (fun j : activeSet (-V) bi w => (-V) j)
        = ((fun _ : activeSet (-V) bi w => (-1 : ℝˣ)) • fun j : activeSet (-V) bi w => V j) := by
      funext j k
      simp [Units.smul_def]
    unfold IsLICQ
    rw [he]
    exact h
  obtain ⟨h1, -, -, -, -, h2⟩ := prop_3_2 (isRowMin_iff_isQPMin.1 hw) hS'
  refine ⟨h1, ?_⟩
  have h3 : rowsOf (-V) (activeSet (-V) bi w) = -rowsOf V (activeSet (-V) bi w) := rfl
  conv_lhs => rw [h2]
  rw [xStar, h3, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_mulVec]

/-- **The cost count `O(N_x r³)` of Section 3.2** (arXiv 2606.31662, the cost in the label
"Proposition 3.1: row separability"). Under LICQ in every row, the linear systems (3.7) of the `N_x`
row problems have sizes `|Sᵢ| ≤ r`, so the sum of the cubes of their sizes is at most `N_x r³`. This
is the formal content of the claim: it counts one solve per row with the cubic cost of a dense
solve, and it does not bound the number of active-set iterations, which the paper does not bound
either. -/
theorem row_active_sets_cost {nx nv r : Type*} [Fintype nx] [Fintype nv]
    [Fintype r] {V : Matrix nv r ℝ} {b : Matrix nx nv ℝ} {dK : Matrix nx r ℝ}
    (h : IsKMin V b dK) (hS : ∀ i, IsLICQ V (activeSet (-V) (b i) (dK i))) :
    ∑ i, (activeSet (-V) (b i) (dK i)).card ^ 3 ≤ Fintype.card nx * Fintype.card r ^ 3 := by
  classical
  have h1 := (prop_3_1 V b dK).2.2.1 h
  calc ∑ i, (activeSet (-V) (b i) (dK i)).card ^ 3
      ≤ ∑ _i : nx, Fintype.card r ^ 3 := Finset.sum_le_sum fun i _ =>
        Nat.pow_le_pow_left (row_closed_form (h1 i) (hS i)).1 3
    _ = Fintype.card nx * Fintype.card r ^ 3 := by simp

/-- **The active-set closed form with equality constraints** (arXiv 2606.31662, the use of (3.7) for
(4.5), which is not spelled out in the paper). For the minimiser `x` of (3.6) with `Q = 2 I`, `c =
0` and with `A_eq` present, suppose the rows of `B = [A_S; A_eq]` are independent, where `S` is the
active set. Then `|S| + #(equalities) ≤ r` and `x = Bᵀ (B Bᵀ)⁻¹ z` with `z = [y_S; y_eq]`. -/
theorem active_set_eq [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq n]
    {A : Matrix ι n ℝ} {y : ι → ℝ} {Aeq : Matrix κ n ℝ} {yeq : κ → ℝ} {x : n → ℝ}
    (hx : IsQPMin ((2 : ℝ) • (1 : Matrix n n ℝ)) 0 A y Aeq yeq x)
    (hS : LinearIndependent ℝ fun j => fromRows (rowsOf A (activeSet A y x)) Aeq j) :
    (activeSet A y x).card + Fintype.card κ ≤ Fintype.card n ∧
      x = (fromRows (rowsOf A (activeSet A y x)) Aeq)ᵀ *ᵥ
        ((fromRows (rowsOf A (activeSet A y x)) Aeq *
            (fromRows (rowsOf A (activeSet A y x)) Aeq)ᵀ)⁻¹ *ᵥ
          Sum.elim (fun j : activeSet A y x => y j) yeq) := by
  obtain ⟨lam, nu, hK⟩ := hx.exists_kkt posSemidef_two_smul_one
  have hact : ∀ j ∈ activeSet A y x, (A *ᵥ x) j = y j := fun j hj => (Finset.mem_filter.1 hj).2
  have hsupp : ∀ j, j ∉ activeSet A y x → lam j = 0 := fun j hj =>
    hK.lam_eq_zero fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
  have h1 : fromRows (rowsOf A (activeSet A y x)) Aeq *ᵥ x
      = Sum.elim (fun j : activeSet A y x => y j) yeq := by
    rw [fromRows_mulVec, hK.primal.2]
    congr 1
    funext j
    exact hact j j.2
  have h2 : x = (fromRows (rowsOf A (activeSet A y x)) Aeq)ᵀ *ᵥ
      ((-(1 / 2) : ℝ) • Sum.elim (fun j : activeSet A y x => lam j) nu) := by
    conv_lhs => rw [hK.eq_neg_half]
    rw [transpose_mulVec_of_support hsupp, mulVec_smul]
    congr 1
    funext k
    simp [mulVec, dotProduct, Fintype.sum_sum_type]
  refine ⟨?_, (closed_form_of_rowSpace hS h1 h2).2⟩
  have h3 := hS.fintype_card_le_finrank
  simpa using h3

end ActiveSet

/-! ### Section 4: the correction MMC-PP-S -/

section MMC

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r]

/-- The all-ones vector. -/
def ones (ι : Type*) : ι → ℝ := fun _ => 1

/-- The discrete total mass `𝓜_h = 1ᵀ F 1` of Section 4 of arXiv 2606.31662; the paper drops the
constant `(Δx)^d (Δv)^d` in the same way. -/
noncomputable def massH (F : Matrix nx nv ℝ) : ℝ := ones nx ⬝ᵥ F *ᵥ ones nv

/-- The discrete total momentum `𝓙_h = 1ᵀ F v` of Section 4 of arXiv 2606.31662, for one component
`v` of the velocity nodes; the paper drops the constant `(Δx)^d (Δv)^d` in the same way. -/
noncomputable def momH (v : nv → ℝ) (F : Matrix nx nv ℝ) : ℝ := ones nx ⬝ᵥ F *ᵥ v

/-- The double sum form of the mass in Section 4 of arXiv 2606.31662. -/
lemma massH_eq_sum (F : Matrix nx nv ℝ) : massH F = ∑ i, ∑ j, F i j := by
  simp [massH, ones, dotProduct, mulVec]

/-- The double sum form of the momentum in Section 4 of arXiv 2606.31662. -/
lemma momH_eq_sum (v : nv → ℝ) (F : Matrix nx nv ℝ) : momH v F = ∑ i, ∑ j, F i j * v j := by
  simp [momH, ones, dotProduct, mulVec]

/-- The mass is additive. -/
lemma massH_add (F G : Matrix nx nv ℝ) : massH (F + G) = massH F + massH G := by
  simp [massH, add_mulVec]

/-- The momentum is additive. -/
lemma momH_add (v : nv → ℝ) (F G : Matrix nx nv ℝ) : momH v (F + G) = momH v F + momH v G := by
  simp [momH, add_mulVec]

/-- The constraints (4.1), (4.2), (4.3) of (4.4) in arXiv 2606.31662. Here `M0`, `J0` are the
initial mass and momentum `𝓜_{h,0}`, `𝓙_{h,0}`, and `St` is `S̃`. -/
structure SFeasible (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (St : Matrix r r ℝ)
    (M0 J0 : ℝ) (dS : Matrix r r ℝ) : Prop where
  /-- Positivity (4.1). -/
  pos : ∀ i j, -(X * St * Vᵀ) i j ≤ (X * dS * Vᵀ) i j
  /-- Mass (4.2). -/
  mass : massH (X * dS * Vᵀ) = M0 - massH (X * St * Vᵀ)
  /-- Momentum (4.3). -/
  mom : momH v (X * dS * Vᵀ) = J0 - momH v (X * St * Vᵀ)

/-- `δS` solves (4.4) of arXiv 2606.31662. -/
def IsSMin (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (St : Matrix r r ℝ) (M0 J0 : ℝ)
    (dS : Matrix r r ℝ) : Prop :=
  SFeasible X V v St M0 J0 dS ∧ ∀ dS', SFeasible X V v St M0 J0 dS' → ‖dS‖ ≤ ‖dS'‖

/-- `M₁ = V ⊗ X` of (4.5) in arXiv 2606.31662. -/
def M1 (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) : Matrix (nv × nx) (r × r) ℝ := V ⊗ₖ X

/-- `M₂ = (1ᵀ V) ⊗ (1ᵀ X)` of (4.5) in arXiv 2606.31662. -/
def M2 (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) : Matrix (Unit × Unit) (r × r) ℝ :=
  (replicateRow Unit (ones nv) * V) ⊗ₖ (replicateRow Unit (ones nx) * X)

/-- `M₃ = (vᵀ V) ⊗ (1ᵀ X)` of (4.5) in arXiv 2606.31662. -/
def M3 (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) : Matrix (Unit × Unit) (r × r) ℝ :=
  (replicateRow Unit v * V) ⊗ₖ (replicateRow Unit (ones nx) * X)

/-- The constraints of (4.5) in arXiv 2606.31662, on a vector `s = vec(δS)`. -/
structure VecFeasible (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (St : Matrix r r ℝ)
    (M0 J0 : ℝ) (s : r × r → ℝ) : Prop where
  /-- `M₁ vec(δS) ⪰ -M₁ vec(S̃)`. -/
  pos : ∀ p, -(M1 X V *ᵥ vec St) p ≤ (M1 X V *ᵥ s) p
  /-- `M₂ vec(δS) = 𝓜_{h,0} - M₂ vec(S̃)`. -/
  mass : M2 X V *ᵥ s = (fun _ => M0) - M2 X V *ᵥ vec St
  /-- `M₃ vec(δS) = 𝓙_{h,0} - M₃ vec(S̃)`. -/
  mom : M3 X V v *ᵥ s = (fun _ => J0) - M3 X V v *ᵥ vec St

/-- `s` solves (4.5) of arXiv 2606.31662. -/
def IsVecMin (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (St : Matrix r r ℝ) (M0 J0 : ℝ)
    (s : r × r → ℝ) : Prop :=
  VecFeasible X V v St M0 J0 s ∧ ∀ s', VecFeasible X V v St M0 J0 s' → l2 s ≤ l2 s'

/-- **Proposition 4.1** (arXiv 2606.31662, label "MMC-PP-S correction (4.4) / Prop. 4.1", the `vec`
identity): `vec(A B C) = (Cᵀ ⊗ A) vec(B)`, where `vec` stacks columns. This is Mathlib's
`Matrix.kronecker_mulVec_vec`. -/
theorem prop_4_1 {l m n p : Type*} [Fintype m] [Fintype n] (A : Matrix l m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n p ℝ) : vec (A * B * C) = (Cᵀ ⊗ₖ A) *ᵥ vec B := by
  rw [kronecker_mulVec_vec, transpose_transpose]

/-- The value of a Kronecker product of two row vectors on `vec dS`. -/
lemma row_kron_apply (a : nx → ℝ) (b : nv → ℝ) (X : Matrix nx r ℝ) (V : Matrix nv r ℝ)
    (dS : Matrix r r ℝ) (p : Unit × Unit) :
    (((replicateRow Unit b * V) ⊗ₖ (replicateRow Unit a * X)) *ᵥ vec dS) p
      = a ⬝ᵥ (X * dS * Vᵀ) *ᵥ b := by
  rw [kronecker_mulVec_vec]
  have h : (replicateRow Unit a * X) * dS * (replicateRow Unit b * V)ᵀ
      = replicateRow Unit a * (X * dS * Vᵀ) * (replicateRow Unit b)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [h]
  simp only [vec, Matrix.mul_apply, replicateRow_apply, transpose_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl
    fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype nx] [Fintype nv] in
/-- `M₁ vec(δS) = vec(X δS Vᵀ)`, entry by entry. -/
lemma M1_mulVec_vec (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (dS : Matrix r r ℝ) (j : nv) (i : nx) :
    (M1 X V *ᵥ vec dS) (j, i) = (X * dS * Vᵀ) i j := by
  rw [M1, kronecker_mulVec_vec]
  rfl

/-- `M₂ vec(δS)` is the mass of `X δS Vᵀ`. -/
lemma M2_mulVec_vec (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (dS : Matrix r r ℝ)
    (p : Unit × Unit) : (M2 X V *ᵥ vec dS) p = massH (X * dS * Vᵀ) :=
  row_kron_apply _ _ X V dS p

/-- `M₃ vec(δS)` is the momentum of `X δS Vᵀ`. -/
lemma M3_mulVec_vec (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (dS : Matrix r r ℝ)
    (p : Unit × Unit) : (M3 X V v *ᵥ vec dS) p = momH v (X * dS * Vᵀ) :=
  row_kron_apply _ _ X V dS p

omit [Fintype nx] [Fintype nv] in
/-- `‖vec(δS)‖₂ = ‖δS‖_F`. -/
lemma l2_vec (dS : Matrix r r ℝ) : l2 (vec dS) = ‖dS‖ := by
  have h : l2 (vec dS) ^ 2 = ‖dS‖ ^ 2 := by
    rw [l2_sq, Frobenius.norm_sq_eq_sum, dotProduct, Fintype.sum_prod_type, Finset.sum_comm]
    simp [vec, sq]
  exact (pow_left_inj₀ (l2_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The constraints of (4.4) on `δS` are those of (4.5) on `vec(δS)`. -/
lemma sFeasible_iff_vecFeasible {X : Matrix nx r ℝ} {V : Matrix nv r ℝ} {v : nv → ℝ}
    {St dS : Matrix r r ℝ} {M0 J0 : ℝ} :
    SFeasible X V v St M0 J0 dS ↔ VecFeasible X V v St M0 J0 (vec dS) := by
  constructor
  · intro h
    refine ⟨fun ⟨j, i⟩ => ?_, ?_, ?_⟩
    · simpa [M1_mulVec_vec] using h.pos i j
    · funext p
      simp [M2_mulVec_vec, h.mass]
    · funext p
      simp [M3_mulVec_vec, h.mom]
  · intro h
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · simpa [M1_mulVec_vec] using h.pos (j, i)
    · have h1 := congrFun h.mass ((), ())
      simpa [M2_mulVec_vec] using h1
    · have h1 := congrFun h.mom ((), ())
      simpa [M3_mulVec_vec] using h1

/-- `A_eq = [M₂; M₃]` of the QP form of (4.5). -/
def eqMatrix (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) :
    Matrix ((Unit × Unit) ⊕ (Unit × Unit)) (r × r) ℝ :=
  fromRows (M2 X V) (M3 X V v)

/-- `y_eq` of the QP form of (4.5). -/
noncomputable def eqRhs (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ) (St : Matrix r r ℝ)
    (M0 J0 : ℝ) : (Unit × Unit) ⊕ (Unit × Unit) → ℝ :=
  Sum.elim ((fun _ => M0) - M2 X V *ᵥ vec St) ((fun _ => J0) - M3 X V v *ᵥ vec St)

/-- The constraints of (4.5) are those of the QP (3.6) with `A = -M₁`, `A_eq = [M₂; M₃]`. -/
lemma vecFeasible_iff_qpFeasible {X : Matrix nx r ℝ} {V : Matrix nv r ℝ}
    {v : nv → ℝ} {St : Matrix r r ℝ} {M0 J0 : ℝ} {s : r × r → ℝ} :
    VecFeasible X V v St M0 J0 s ↔
      QPFeasible (-M1 X V) (M1 X V *ᵥ vec St) (eqMatrix X V v) (eqRhs X V v St M0 J0) s := by
  constructor
  · intro h
    refine ⟨fun p => ?_, ?_⟩
    · have := h.pos p
      simp only [neg_mulVec, Pi.neg_apply]
      linarith
    · rw [eqMatrix, fromRows_mulVec, h.mass, h.mom, eqRhs]
  · rintro ⟨h1, h2⟩
    rw [eqMatrix, fromRows_mulVec, eqRhs] at h2
    refine ⟨fun p => ?_, ?_, ?_⟩
    · have := h1 p
      simp only [neg_mulVec, Pi.neg_apply] at this
      linarith
    · funext p
      exact congrFun h2 (Sum.inl p)
    · funext p
      exact congrFun h2 (Sum.inr p)

/-- **The reformulation (4.5) of (4.4)** (arXiv 2606.31662, label "MMC-PP-S correction (4.4) / Prop.
4.1"). With `M₁ = V ⊗ X`, `M₂ = (1ᵀ V) ⊗ (1ᵀ X)`, `M₃ = (vᵀ V) ⊗ (1ᵀ X)`: the constraints of (4.4)
on `δS` are those of (4.5) on `vec(δS)`, `‖vec(δS)‖₂ = ‖δS‖_F`, `δS` solves (4.4) iff `vec(δS)`
solves (4.5), and (4.5) is the standard QP (3.6) in `r²` variables with `Q = 2 I`, `c = 0`, `A =
-M₁`, `y = M₁ vec(S̃)`, and the two equality constraints `[M₂; M₃] s = y_eq`. -/
theorem mmc_vec_reformulation [DecidableEq r] (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (v : nv → ℝ)
    (St dS : Matrix r r ℝ) (M0 J0 : ℝ) :
    (SFeasible X V v St M0 J0 dS ↔ VecFeasible X V v St M0 J0 (vec dS)) ∧
      l2 (vec dS) = ‖dS‖ ∧
      (IsSMin X V v St M0 J0 dS ↔ IsVecMin X V v St M0 J0 (vec dS)) ∧
      ∀ s, IsVecMin X V v St M0 J0 s ↔
        IsQPMin ((2 : ℝ) • (1 : Matrix (r × r) (r × r) ℝ)) 0 (-M1 X V) (M1 X V *ᵥ vec St)
          (eqMatrix X V v) (eqRhs X V v St M0 J0) s := by
  refine ⟨sFeasible_iff_vecFeasible, l2_vec dS, ⟨?_, ?_⟩, fun s => ?_⟩
  · rintro ⟨h1, h2⟩
    refine ⟨sFeasible_iff_vecFeasible.1 h1, fun s hs => ?_⟩
    obtain ⟨T, rfl⟩ := vec_bijective.2 s
    rw [l2_vec, l2_vec]
    exact h2 _ (sFeasible_iff_vecFeasible.2 hs)
  · rintro ⟨h1, h2⟩
    refine ⟨sFeasible_iff_vecFeasible.2 h1, fun T hT => ?_⟩
    have := h2 _ (sFeasible_iff_vecFeasible.1 hT)
    rwa [l2_vec, l2_vec] at this
  · rw [isQPMin_two_iff]
    simp only [IsVecMin, vecFeasible_iff_qpFeasible]

omit [Fintype nx] [Fintype nv] in
/-- Distributivity for `X (S̃ + δS) Vᵀ`. -/
lemma mul_add_mul_apply (X : Matrix nx r ℝ) (V : Matrix nv r ℝ) (St dS : Matrix r r ℝ) :
    X * (St + dS) * Vᵀ = X * St * Vᵀ + X * dS * Vᵀ := by
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The constraints (4.1), (4.2), (4.3) of arXiv 2606.31662 say exactly that the corrected state `F
= X (S̃ + δS) Vᵀ` is nonnegative and has the mass `𝓜_{h,0}` and momentum `𝓙_{h,0}`. -/
theorem sFeasible_iff_corrected {X : Matrix nx r ℝ} {V : Matrix nv r ℝ} {v : nv → ℝ}
    {St dS : Matrix r r ℝ} {M0 J0 : ℝ} :
    SFeasible X V v St M0 J0 dS ↔
      (∀ i j, 0 ≤ (X * (St + dS) * Vᵀ) i j) ∧ massH (X * (St + dS) * Vᵀ) = M0 ∧
        momH v (X * (St + dS) * Vᵀ) = J0 := by
  simp only [mul_add_mul_apply, massH_add, momH_add, Matrix.add_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := h.pos i j
      linarith
    · rw [h.mass]
      ring
    · rw [h.mom]
      ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · have := h1 i j
      linarith
    · rw [← h2]
      ring
    · rw [← h3]
      ring

/-- **The correction MMC-PP-S** (arXiv 2606.31662, label "MMC-PP-S correction (4.4) / Prop. 4.1",
Algorithm 4.1, step 10). If (4.4) is feasible, it has exactly one solution `δS`, and the corrected
state `F = X (S̃ + δS) Vᵀ` is entrywise nonnegative, has exactly the mass `𝓜_{h,0}` and the momentum
`𝓙_{h,0}`, and has rank at most `r`. The bases `X`, `V` need not be orthonormal here; with
orthonormal bases `mmc_pp_s_closest` adds that `F` is the closest admissible state. Feasibility is a
hypothesis, as in the paper, where its failure triggers the rank increase of step 7 of Algorithm
4.1; see `sFeasible_mono` for that step and `mmc_pp_s_instance` for an instance. -/
theorem mmc_pp_s {X : Matrix nx r ℝ} {V : Matrix nv r ℝ} {v : nv → ℝ}
    {St : Matrix r r ℝ} {M0 J0 : ℝ} (h : ∃ dS, SFeasible X V v St M0 J0 dS) :
    ∃ dS, (∀ dS', IsSMin X V v St M0 J0 dS' ↔ dS' = dS) ∧
      (∀ i j, 0 ≤ (X * (St + dS) * Vᵀ) i j) ∧
      massH (X * (St + dS) * Vᵀ) = M0 ∧
      momH v (X * (St + dS) * Vᵀ) = J0 ∧
      (X * (St + dS) * Vᵀ).rank ≤ Fintype.card r := by
  classical
  obtain ⟨dS₀, hS₀⟩ := h
  have hq : ∃ w, QPFeasible (-M1 X V) (M1 X V *ᵥ vec St) (eqMatrix X V v)
      (eqRhs X V v St M0 J0) w :=
    ⟨vec dS₀, vecFeasible_iff_qpFeasible.1 (sFeasible_iff_vecFeasible.1 hS₀)⟩
  obtain ⟨s, hs, hu⟩ := existsUnique_isQPMin_two hq
  obtain ⟨dS, rfl⟩ := vec_bijective.2 s
  have hmin : IsSMin X V v St M0 J0 dS := by
    have h1 := (mmc_vec_reformulation X V v St dS M0 J0).2.2
    exact h1.1.2 ((h1.2 _).2 hs)
  obtain ⟨h1, h2, h3⟩ := sFeasible_iff_corrected.1 hmin.1
  refine ⟨dS, fun dS' => ⟨fun h' => ?_, ?_⟩, h1, h2, h3, ?_⟩
  · have h4 := mmc_vec_reformulation X V v St dS' M0 J0
    exact vec_bijective.1 (hu _ ((h4.2.2.2 _).1 (h4.2.2.1.1 h')))
  · rintro rfl
    exact hmin
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- **Closeness of the corrected state** (arXiv 2606.31662, the purpose of (4.4), cf. (3.2)). For
orthonormal bases `‖X δS Vᵀ‖_F = ‖δS‖_F`, so the solution of (4.4) makes the smallest change of `F̃
= X S̃ Vᵀ` in the Frobenius norm among all admissible corrections, and the error grows by at most
`‖δS‖_F`. In the paper this is the reason for the objective, for `K` in (3.2). -/
theorem mmc_pp_s_closest [DecidableEq r] {X : Matrix nx r ℝ} {V : Matrix nv r ℝ} {v : nv → ℝ}
    {St dS : Matrix r r ℝ} {M0 J0 : ℝ} (hX : Xᵀ * X = 1) (hV : Vᵀ * V = 1)
    (h : IsSMin X V v St M0 J0 dS) :
    (∀ dS', SFeasible X V v St M0 J0 dS' →
      ‖X * (St + dS) * Vᵀ - X * St * Vᵀ‖ ≤ ‖X * (St + dS') * Vᵀ - X * St * Vᵀ‖) ∧
    ∀ Fa : Matrix nx nv ℝ, ‖X * (St + dS) * Vᵀ - Fa‖ ≤ ‖X * St * Vᵀ - Fa‖ + ‖dS‖ := by
  have hn : ∀ T : Matrix r r ℝ, ‖X * (St + T) * Vᵀ - X * St * Vᵀ‖ = ‖T‖ := fun T => by
    rw [mul_add_mul_apply, add_sub_cancel_left, Frobenius.norm_mul_transpose_of_orthonormal hV,
      Frobenius.norm_mul_of_orthonormal hX]
  refine ⟨fun dS' hf => ?_, fun Fa => ?_⟩
  · rw [hn, hn]
    exact h.2 dS' hf
  · have h1 : X * (St + dS) * Vᵀ - Fa
        = (X * St * Vᵀ - Fa) + (X * (St + dS) * Vᵀ - X * St * Vᵀ) := by
      abel
    rw [h1]
    exact (norm_add_le _ _).trans_eq (by rw [hn])

/-- **KKT conditions and active set of (4.5)** (arXiv 2606.31662, Section 4, "its structure is
similar to (3.4)"). A vector `s` solves (4.5) iff it satisfies the KKT conditions of the QP. If the
rows of `[A_S; M₂; M₃]` are independent, where `S` is the active set, then `|S| + 2 ≤ r²`, so the
system (3.7) of (4.5) has size at most `r²`, which is the claimed cost `O((r²)³) = O(r⁶)` of one
solve, and `s` is given by the closed form (with the sign corrected as in `prop_3_2`). -/
theorem mmc_kkt_active_set [DecidableEq r] [DecidableEq nx] [DecidableEq nv] {X : Matrix nx r ℝ}
    {V : Matrix nv r ℝ} {v : nv → ℝ} {St : Matrix r r ℝ} {M0 J0 : ℝ} {s : r × r → ℝ} :
    (IsVecMin X V v St M0 J0 s ↔ ∃ lam nu, IsKKT ((2 : ℝ) • (1 : Matrix (r × r) (r × r) ℝ)) 0
      (-M1 X V) (M1 X V *ᵥ vec St) (eqMatrix X V v) (eqRhs X V v St M0 J0) s lam nu) ∧
    (IsVecMin X V v St M0 J0 s →
      LinearIndependent ℝ (fun j => fromRows
        (rowsOf (-M1 X V) (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s)) (eqMatrix X V v) j) →
      (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s).card + 2 ≤ Fintype.card r ^ 2 ∧
      s = (fromRows (rowsOf (-M1 X V) (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s))
          (eqMatrix X V v))ᵀ *ᵥ
        ((fromRows (rowsOf (-M1 X V) (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s)) (eqMatrix X V v) *
          (fromRows (rowsOf (-M1 X V) (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s))
            (eqMatrix X V v))ᵀ)⁻¹ *ᵥ
          Sum.elim (fun j : activeSet (-M1 X V) (M1 X V *ᵥ vec St) s => (M1 X V *ᵥ vec St) j)
            (eqRhs X V v St M0 J0))) := by
  have h0 := fun s => (mmc_vec_reformulation X V v St (0 : Matrix r r ℝ) M0 J0).2.2.2 s
  refine ⟨?_, fun hs hS => ?_⟩
  · rw [h0]
    exact isQPMin_iff_exists_kkt posSemidef_two_smul_one
  · obtain ⟨h1, h2⟩ := active_set_eq ((h0 s).1 hs) hS
    refine ⟨?_, h2⟩
    simpa [sq] using h1

/-- **The rank increase of Algorithm 4.1 preserves feasibility** (arXiv 2606.31662, Section 4: "we
can increase the rank `r` to enhance the feasibility of (4.5)"). If the columns of `X`, `V` are
combinations of the columns of `X'`, `V'` (for instance the first `r₁` of the `r₁ + 1` columns), and
(4.4) is feasible for `X`, `V`, then it is feasible for `X'`, `V'`, whatever the `S̃` is. -/
theorem sFeasible_mono {r' : Type*} [Fintype r'] {X : Matrix nx r ℝ} {V : Matrix nv r ℝ}
    {X' : Matrix nx r' ℝ} {V' : Matrix nv r' ℝ} {v : nv → ℝ} {M0 J0 : ℝ}
    (hX : ∃ P : Matrix r' r ℝ, X = X' * P) (hV : ∃ R : Matrix r' r ℝ, V = V' * R)
    (St : Matrix r r ℝ) (St' : Matrix r' r' ℝ) (h : ∃ dS, SFeasible X V v St M0 J0 dS) :
    ∃ dS', SFeasible X' V' v St' M0 J0 dS' := by
  obtain ⟨P, rfl⟩ := hX
  obtain ⟨R, rfl⟩ := hV
  obtain ⟨dS, hdS⟩ := h
  refine ⟨P * (St + dS) * Rᵀ - St', sFeasible_iff_corrected.2 ?_⟩
  have h1 : X' * (St' + (P * (St + dS) * Rᵀ - St')) * V'ᵀ
      = X' * P * (St + dS) * (V' * R)ᵀ := by
    rw [add_sub_cancel, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1]
  exact sFeasible_iff_corrected.1 hdS

/-- **An instance of MMC-PP-S** (arXiv 2606.31662, (4.4)): the hypotheses of `mmc_pp_s` and
`mmc_pp_s_closest` can hold with a truly negative state. For `N_x = N_v = 2`, `r = 1`, `X = V = (1,
1)ᵀ/√2`, `v = (-1, 1)`, `S̃ = -1`, the state `F̃ = X S̃ Vᵀ` is negative everywhere, and `δS = 2` is
feasible for `𝓜_{h,0} = 2`, `𝓙_{h,0} = 0`. -/
theorem mmc_pp_s_instance :
    ∃ (X V : Matrix (Fin 2) (Fin 1) ℝ) (v : Fin 2 → ℝ) (St dS : Matrix (Fin 1) (Fin 1) ℝ),
      Xᵀ * X = 1 ∧ Vᵀ * V = 1 ∧ (∀ i j, (X * St * Vᵀ) i j < 0) ∧ SFeasible X V v St 2 0 dS := by
  have hs : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  have hE : (!![Real.sqrt 2 / 2; Real.sqrt 2 / 2] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ *
      !![Real.sqrt 2 / 2; Real.sqrt 2 / 2] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linarith
  have hF : ∀ c : ℝ, (!![Real.sqrt 2 / 2; Real.sqrt 2 / 2] : Matrix (Fin 2) (Fin 1) ℝ) * !![c] *
      (!![Real.sqrt 2 / 2; Real.sqrt 2 / 2] : Matrix (Fin 2) (Fin 1) ℝ)ᵀ
        = Matrix.of fun _ _ => c / 2 := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> linear_combination c * hs
  refine ⟨!![Real.sqrt 2 / 2; Real.sqrt 2 / 2], !![Real.sqrt 2 / 2; Real.sqrt 2 / 2], ![-1, 1],
    !![-1], !![2], hE, hE, fun i j => ?_, sFeasible_iff_corrected.2 ?_⟩
  · rw [hF]
    norm_num
  · have h1 : (!![-1] + !![2] : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
      ext i j
      fin_cases i
      fin_cases j
      norm_num
    rw [h1, hF]
    refine ⟨fun i j => by norm_num, ?_, ?_⟩
    · rw [massH_eq_sum]
      simp
    · rw [momH_eq_sum]
      simp [Fin.sum_univ_two]

/-- **An instance of the active-set statement for (4.5)** (arXiv 2606.31662, Section 4): the
hypotheses of the second part of `mmc_kkt_active_set` can hold. For `N_x = N_v = r = 2`, `X = V =
I`, `v = (-1, 1)`, `S̃ = 1 1ᵀ`, `𝓜_{h,0} = 4`, `𝓙_{h,0} = 0`, the zero correction solves (4.5), no
positivity constraint is active, and the rows of `M₂`, `M₃` are independent. -/
theorem mmc_active_set_instance :
    ∃ (X V : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (St : Matrix (Fin 2) (Fin 2) ℝ)
      (M0 J0 : ℝ) (s : Fin 2 × Fin 2 → ℝ),
      Xᵀ * X = 1 ∧ Vᵀ * V = 1 ∧ IsVecMin X V v St M0 J0 s ∧
      LinearIndependent ℝ (fun j => fromRows
        (rowsOf (-M1 X V) (activeSet (-M1 X V) (M1 X V *ᵥ vec St) s)) (eqMatrix X V v) j) := by
  have hSt : (1 : Matrix (Fin 2) (Fin 2) ℝ) * (Matrix.of fun _ _ => 1) *
      (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = Matrix.of fun _ _ => 1 := by simp
  have hS0 : IsSMin (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-1, 1]
      (Matrix.of fun _ _ => 1) 4 0 0 := by
    refine ⟨⟨fun i j => ?_, ?_, ?_⟩, fun dS' _ => by simp⟩
    · rw [hSt]
      simp
    · rw [hSt, massH_eq_sum, massH_eq_sum]
      simp
      norm_num
    · rw [hSt, momH_eq_sum, momH_eq_sum]
      simp [Fin.sum_univ_two]
  have hmin := (mmc_vec_reformulation (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-1, 1] (Matrix.of fun _ _ => 1) 0 4 0).2.2.1.1 hS0
  have hempty : IsEmpty ↥(activeSet
      (-M1 (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (M1 (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
        vec (Matrix.of fun _ _ => 1)) (vec 0)) := by
    refine ⟨fun j => ?_⟩
    obtain ⟨⟨k, l⟩, hj⟩ := j
    have h1 := (Finset.mem_filter.1 hj).2
    rw [neg_mulVec, Pi.neg_apply, M1_mulVec_vec, M1_mulVec_vec, hSt] at h1
    simp at h1
  have hM2 : ∀ (u : Unit × Unit) (p : Fin 2 × Fin 2),
      M2 (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) u p = 1 := by
    intro u p
    simp [M2, ones]
  have hM3 : ∀ (u : Unit × Unit) (p : Fin 2 × Fin 2),
      M3 (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-1, 1] u p
        = (![-1, 1] : Fin 2 → ℝ) p.1 := by
    intro u p
    simp [M3, ones]
  have hLI : LinearIndependent ℝ fun j =>
      eqMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-1, 1] j := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    rw [Fintype.sum_sum_type] at hg
    have h00 := congrFun hg (0, 0)
    have h10 := congrFun hg (1, 0)
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eqMatrix,
      fromRows_apply_inl, fromRows_apply_inr, hM2, hM3, Pi.zero_apply] at h00 h10
    simp at h00 h10
    rcases i with u | u
    · have h1 : ∑ x, g (Sum.inl x) = g (Sum.inl u) := Fintype.sum_subsingleton _ u
      linarith
    · have h1 : ∑ x, g (Sum.inr x) = g (Sum.inr u) := Fintype.sum_subsingleton _ u
      linarith
  refine ⟨1, 1, ![-1, 1], Matrix.of fun _ _ => 1, 4, 0, vec 0, by simp, by simp, hmin, ?_⟩
  have he : (fun j => fromRows (rowsOf (-M1 (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (activeSet (-M1 (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) (M1 (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ vec (Matrix.of fun _ _ => 1)) (vec 0)))
      (eqMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ) ![-1, 1]) j)
      ∘ (Equiv.emptySum _ _).symm
      = fun j => eqMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        ![-1, 1] j := rfl
  exact (linearIndependent_equiv (Equiv.emptySum _ _).symm).1 (he ▸ hLI)

end MMC

/-! ### Section 3: the correction PP-KL -/

section PPKL

variable {nx nv r : Type*} [Fintype nx] [Fintype nv] [Fintype r]

omit [Fintype nx] [Fintype nv] in
/-- The positivity condition (3.1) of arXiv 2606.31662: `F = (K̃ + δK) Vᵀ ⪰ 0` is equivalent to the
constraint `-δK Vᵀ ⪯ K̃ Vᵀ` of (3.3). -/
theorem eq_3_1 {V : Matrix nv r ℝ} {Kt dK : Matrix nx r ℝ} :
    (∀ i j, 0 ≤ ((Kt + dK) * Vᵀ) i j) ↔ KFeasible V (Kt * Vᵀ) dK := by
  simp only [KFeasible, Matrix.add_mul, Matrix.add_apply, Matrix.neg_apply]
  exact forall₂_congr fun i j => by constructor <;> intro h <;> linarith

/-- The error bound (3.2) of arXiv 2606.31662, with the bound `‖δF‖_F ≤ ‖δK‖_F ‖V‖_F` that follows
it. The last part is an addition to the paper: for orthonormal `V` even `‖δF‖_F = ‖δK‖_F`. -/
theorem eq_3_2 [DecidableEq r] (V : Matrix nv r ℝ) (Kt dK : Matrix nx r ℝ) (Fa : Matrix nx nv ℝ) :
    ‖(Kt + dK) * Vᵀ - Fa‖ ≤ ‖Kt * Vᵀ - Fa‖ + ‖dK * Vᵀ‖ ∧
      ‖dK * Vᵀ‖ ≤ ‖dK‖ * ‖V‖ ∧ (Vᵀ * V = 1 → ‖dK * Vᵀ‖ = ‖dK‖) := by
  refine ⟨?_, ?_, fun hV => Frobenius.norm_mul_transpose_of_orthonormal hV dK⟩
  · have h1 : (Kt + dK) * Vᵀ - Fa = (Kt * Vᵀ - Fa) + dK * Vᵀ := by
      rw [Matrix.add_mul]
      abel
    rw [h1]
    exact norm_add_le _ _
  · exact (Frobenius.norm_mul_le _ _).trans_eq (by rw [Frobenius.norm_transpose])

/-- **The correction PP-KL** (arXiv 2606.31662, (3.3), steps 5 to 7 of Algorithm 3.1). Problem (3.3)
has exactly one solution `δK`, whose rows are the solutions of (3.4) by `prop_3_1`. Any
factorisation `K̃ + δK = X S`, e.g. by QR, gives an entrywise nonnegative `F = X S Vᵀ` of rank at
most `r`. The same holds for the correction (3.5) of `L`, with `X` in the role of `V`.

Remark 3.4 of the paper says that solvability of (3.3) and (3.5) is not guaranteed. As stated this
is too cautious, since `δK = -K̃` is always feasible (this is the library's `ppKL_feasible_unique`).
The remark does apply to the constraint `F ⪰ ε 1` of Remark 3.3, which is `KFeasible` with `b = K̃
Vᵀ - ε 1`, and then `existsUnique_isKMin` applies whenever the rows are feasible; compare the
library's `gordan_positive_range`. -/
theorem pp_kl (V : Matrix nv r ℝ) (Kt : Matrix nx r ℝ) :
    ∃ dK, (∀ dK', IsKMin V (Kt * Vᵀ) dK' ↔ dK' = dK) ∧
      ∀ (X : Matrix nx r ℝ) (S : Matrix r r ℝ), Kt + dK = X * S →
        (∀ i j, 0 ≤ (X * S * Vᵀ) i j) ∧ (X * S * Vᵀ).rank ≤ Fintype.card r := by
  have hf : ∀ i, ∃ w, RowFeasible V ((Kt * Vᵀ) i) w := fun i =>
    ⟨-Kt i, fun j => by
      rw [mul_transpose_apply, mulVec_neg, Pi.neg_apply, neg_neg]⟩
  obtain ⟨dK, hK, hu⟩ := existsUnique_isKMin hf
  refine ⟨dK, fun dK' => ⟨hu dK', fun h => h ▸ hK⟩, fun X S hXS => ?_⟩
  rw [← hXS]
  refine ⟨eq_3_1.2 hK.1, (Matrix.rank_mul_le_left _ _).trans ?_⟩
  rw [hXS]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

end PPKL


end LeanDLRA.Literature.P2606_31662

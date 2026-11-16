import LeanDLRA.Tensor.Tucker.Basic
import LeanDLRA.Integrators.TuckerBUGCore
import LeanDLRA.Matrix.Orthonormal

/-!
# The Tucker BUG step as a step relation

This file states one step of the basis-update & Galerkin (BUG) integrator for tensors in Tucker
format with fixed multilinear rank (Ceruti and Lubich, arXiv:2010.02022, §5) as a relation
between the old value `Y₀` and the new value `Y₁` (`StepRel` on `Tensor ι`), and gives its
invariance, its locality and its local error near a reference solution. The step at the level
of orthogonal projectors and its analysis are `IsTuckerBUGStepCore` and
`IsTuckerBUGStepCore.hasLocalError_of_tube` in `LeanDLRA/Integrators/TuckerBUGCore.lean`; runs of
the integrator are in `LeanDLRA/Tensor/Tucker/BUGRun.lean`.

**The step.** For every mode `i`, the co-range basis `V₀ i` has `r i` orthonormal columns indexed
by the multi-indices of the other modes, and its projector `Q₀ i = actOn (· ≠ i) (V₀ i V₀ iᵀ)`
fixes `Y₀`. The K-step of mode `i` solves `Ẏ = Q₀ i F(t, Y)` from `Y₀`; the new mode basis
`U₁ i` has `r i` orthonormal columns, and its mode projector `P₁ i = modeProj i (U₁ i)` fixes the
result of the K-step. The Galerkin step solves `Ẏ = Π F(t, Y)` from `Π Y₀`, where `Π` is the
product of the `P₁ i`; its result is `Y₁` (`TuckerBUG.stepRel`). The admissible values are the
tensors of multilinear rank at most `r` (`Tensor.ModeRankLE`), and every step ends at such a
tensor (`TuckerBUG.stepRel.modeRankLE`).

## Main definitions

* `Tensor.ModeRankLE r Y`: for every mode `i` there is a basis with `r i` orthonormal columns
  whose mode projector fixes `Y` (multilinear rank at most `r`, without unfoldings).
* `TuckerBUG.stepRel F r`: the Tucker BUG step with multilinear rank `r`.
* `TuckerBUG.normalTriples r`: the triples (new mode projector, old co-range projector, tensor)
  at which the step evaluates the normal part of the field.

## Main results

* `Tensor.rank_unfold_ne`: the unfolding for the modes other than `i` and the mode-`i` unfolding
  have the same rank.
* `Tensor.exists_modeProj_eq_self`, `Tensor.ModeRankLE.exists_coRange`: bases that fix a tensor
  exist as soon as the rank of the corresponding unfolding is small enough.
* `Tensor.isTuckerBUGStepCore_of_orthonormal`: the data of a step form a step
  `IsTuckerBUGStepCore`; orthogonality and commutation of the projectors are derived.
* `TuckerBUG.stepRel.modeRankLE`: the result of a step has multilinear rank at most `r`.
* `TuckerBUG.stepRel_tubeExt_iff_of_near`: if `‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, the tube
  extension `tubeExt F A a b ρ` has the same steps as `F`.
* `TuckerBUG.stepRel.hasLocalError_of_tube`: the local error
  `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))`, `c₁ = tuckerC₁ d L H`, `c₂ = tuckerC₂ d L B H`, if the normal
  part of `F` is at most `ε` at the triples `TuckerBUG.normalTriples r` in the tube.

## Implementation notes

The relation quantifies the bases, the trajectories of the K-steps and the trajectory of the
Galerkin step; the multilinear rank `r` is a parameter and no state other than the tensor is
carried. The normal part is needed at the results `YK i t₁` of the K-steps, which are fixed by
the new mode projector (by the step) and by the old co-range projector (a solution of
`Ẏ = Q₀ i F(t, Y)` that starts in the range of `Q₀ i` stays there,
`ODESolution.galerkin_mem_range`).

## References

* G. Ceruti, Ch. Lubich, *An unconventional robust integrator for dynamical low-rank
  approximation*, arXiv:2010.02022 (BIT Numer. Math. 2022), §5.
-/

open Set
open scoped Matrix

namespace LeanDLRA

namespace Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)]

/-! ### The mode-`i` unfolding and the unfolding for the other modes -/

section Unfold

omit [∀ i, Fintype (ι i)] in
/-- The unfolding for the modes other than `i` is the transpose of the mode-`i` unfolding, up to
the names of the multi-indices of mode `i`. -/
theorem unfold_ne_eq_submatrix (i : Fin d) (X : Tensor ι) :
    unfold (· ≠ i) X = ((unfold (· = i) X)ᵀ).submatrix (fun a => a)
      (fun (b : ∀ k : {k : Fin d // ¬ k ≠ i}, ι k) (k : {k : Fin d // k = i}) =>
        b ⟨k.1, not_not.2 k.2⟩) := by
  ext a b
  have hm : merge (· ≠ i) a b =
      merge (· = i) (fun k : {k : Fin d // k = i} => b ⟨k.1, not_not.2 k.2⟩) a := by
    funext k
    by_cases h : k = i
    · subst h
      simp [merge]
    · simp [merge, h]
  simp only [unfold_apply, Matrix.submatrix_apply, Matrix.transpose_apply, hm]

omit [∀ i, Fintype (ι i)] in
/-- The mode-`i` unfolding is the transpose of the unfolding for the other modes, up to the names
of the multi-indices of mode `i`. -/
theorem unfold_eq_eq_submatrix (i : Fin d) (X : Tensor ι) :
    unfold (· = i) X = ((unfold (· ≠ i) X)ᵀ).submatrix
      (fun (c : ∀ k : {k : Fin d // k = i}, ι k) (k : {k : Fin d // ¬ k ≠ i}) =>
        c ⟨k.1, not_not.1 k.2⟩) (fun a => a) := by
  ext c a
  have hm : merge (· = i) c a =
      merge (· ≠ i) a (fun k : {k : Fin d // ¬ k ≠ i} => c ⟨k.1, not_not.1 k.2⟩) := by
    funext k
    by_cases h : k = i
    · subst h
      simp [merge]
    · simp [merge, h]
  simp only [unfold_apply, Matrix.submatrix_apply, Matrix.transpose_apply, hm]

/-- The unfolding for the modes other than `i` and the mode-`i` unfolding have the same rank. -/
theorem rank_unfold_ne (i : Fin d) (X : Tensor ι) :
    (unfold (· ≠ i) X).rank = (unfold (· = i) X).rank := by
  apply le_antisymm
  · rw [unfold_ne_eq_submatrix]
    exact (Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_transpose _).le
  · rw [unfold_eq_eq_submatrix]
    exact (Matrix.rank_submatrix_le _ _ _).trans (Matrix.rank_transpose _).le

/-- The mode-`i` projector of `U` is the map acting on mode `i` by `U' U'ᵀ`, where `U'` is `U`
with its rows indexed by the multi-indices of the single mode `i`. -/
theorem modeProj_eq_actOn (i : Fin d) {r : Type*} [Fintype r] (U : Matrix (ι i) r ℝ) :
    modeProj i U = actOn (· = i) (U.submatrix (modeEquiv i) (fun a => a) *
      (U.submatrix (modeEquiv i) (fun a => a))ᵀ) := by
  rw [modeProj, modeAct]
  congr 1

/-- A tensor fixed by the mode-`i` projector of a matrix with `s` columns has a mode-`i`
unfolding of rank at most `s`. -/
theorem rank_unfold_le_of_modeProj_eq_self (i : Fin d) {s : Type*} [Fintype s]
    {U : Matrix (ι i) s ℝ} {X : Tensor ι} (h : modeProj i U X = X) :
    (unfold (· = i) X).rank ≤ Fintype.card s := by
  -- `rank (W Wᵀ M) ≤ card s`, for every `Fintype` structure on the multi-indices of mode `i`
  -- (`unfold_actOn` carries the one of `Subtype.fintype`, synthesis gives `Fintype.subtypeEq`)
  have key : ∀ {_ : Fintype (∀ k : {k : Fin d // k = i}, ι k)}
      {_ : Fintype (∀ k : {k : Fin d // ¬ k = i}, ι k)}
      (W : Matrix (∀ k : {k : Fin d // k = i}, ι k) s ℝ)
      (M : Matrix (∀ k : {k : Fin d // k = i}, ι k) (∀ k : {k : Fin d // ¬ k = i}, ι k) ℝ),
      (W * Wᵀ * M).rank ≤ Fintype.card s := fun W _ =>
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_le_card_width W))
  conv_lhs => rw [← h, modeProj_eq_actOn, unfold_actOn]
  exact key _ _

/-- A tensor fixed by the co-range projector of a matrix with `s` columns has an unfolding for
the modes other than `i` of rank at most `s`. -/
theorem rank_unfold_ne_le_of_actOn_eq_self (i : Fin d) {s : Type*} [Fintype s]
    {V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) s ℝ} {X : Tensor ι}
    (h : actOn (· ≠ i) (V * Vᵀ) X = X) : (unfold (· ≠ i) X).rank ≤ Fintype.card s := by
  conv_lhs => rw [← h, unfold_actOn]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
    (Matrix.rank_le_card_width _))

/-- **A co-range basis that fixes a tensor.** If the unfolding of `X` for the modes other than
`i` has rank at most `q` and `q` is at most the number of multi-indices of these modes, then a
matrix `V` with `q` orthonormal columns exists whose co-range projector fixes `X`. -/
theorem exists_coRange_eq_self (i : Fin d) {q : ℕ} {X : Tensor ι}
    (h : (unfold (· ≠ i) X).rank ≤ q)
    (hq : q ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k)) :
    ∃ V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin q) ℝ,
      Vᵀ * V = 1 ∧ actOn (· ≠ i) (V * Vᵀ) X = X := by
  obtain ⟨V, hV, hcap⟩ := exists_orthonormal_capture _ h hq
  exact ⟨V, hV, unfold_injective (· ≠ i) (by rw [unfold_actOn]; convert hcap)⟩

/-- **A mode basis that fixes a tensor.** If the mode-`i` unfolding of `X` has rank at most `q`
and `q ≤ card (ι i)`, then a matrix `U` with `q` orthonormal columns exists whose mode-`i`
projector fixes `X`. -/
theorem exists_modeProj_eq_self (i : Fin d) {q : ℕ} {X : Tensor ι}
    (h : (unfold (· = i) X).rank ≤ q) (hq : q ≤ Fintype.card (ι i)) :
    ∃ U : Matrix (ι i) (Fin q) ℝ, Uᵀ * U = 1 ∧ modeProj i U X = X := by
  obtain ⟨U', hU', hcap⟩ := exists_orthonormal_capture _ h
    (hq.trans (Fintype.card_congr (modeEquiv i)).ge)
  refine ⟨U'.submatrix (modeEquiv i).symm (fun a => a), ?_, ?_⟩
  · ext a b
    have e := congrFun (congrFun hU' a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply] at e ⊢
    rw [← e]
    exact Fintype.sum_equiv (modeEquiv i).symm _ _ fun _ => rfl
  · have hsub : (U'.submatrix (modeEquiv i).symm (fun a => a)).submatrix (modeEquiv i)
        (fun a => a) = U' := by
      ext a b
      simp
    rw [modeProj_eq_actOn, hsub]
    -- `hcap` multiplies with the synthesized `Fintype` structure on the multi-indices of mode
    -- `i`, `unfold_actOn` with the one of `Subtype.fintype`; `convert` identifies them
    exact unfold_injective (· = i) (by rw [unfold_actOn]; convert hcap)

end Unfold

/-! ### Multilinear rank -/

section ModeRank

/-- **Multilinear rank at most `r`**, without unfoldings: for every mode `i` there is a matrix
with `r i` orthonormal columns whose mode-`i` projector fixes `Y`. -/
def ModeRankLE (r : Fin d → ℕ) (Y : Tensor ι) : Prop :=
  ∀ i, ∃ U : Matrix (ι i) (Fin (r i)) ℝ, Uᵀ * U = 1 ∧ modeProj i U Y = Y

/-- **A tensor of multilinear rank at most `r` has co-range bases.** For every mode `i` with
`r i` at most the number of multi-indices of the other modes there is a matrix `V` with `r i`
orthonormal columns whose co-range projector `actOn (· ≠ i) (V Vᵀ)` fixes `Y`. -/
theorem ModeRankLE.exists_coRange {r : Fin d → ℕ} {Y : Tensor ι} (hY : ModeRankLE r Y)
    (i : Fin d) (hr : r i ≤ Fintype.card (∀ k : {k : Fin d // k ≠ i}, ι k)) :
    ∃ V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin (r i)) ℝ,
      Vᵀ * V = 1 ∧ actOn (· ≠ i) (V * Vᵀ) Y = Y := by
  obtain ⟨U, -, hU⟩ := hY i
  refine exists_coRange_eq_self i ?_ hr
  rw [rank_unfold_ne]
  simpa using rank_unfold_le_of_modeProj_eq_self i hU

end ModeRank

/-- **The data of a Tucker BUG step form a step `IsTuckerBUGStepCore`.** For mode bases `U₁ i`
and co-range bases `V₀ i` with orthonormal columns, K-step trajectories `YK i` that start at `Y₀`
and whose results are fixed by the new mode projectors, and a Galerkin trajectory `YS` started at
`Π Y₀`, the step is a step of the BUG integrator for `d` modes with `Q₀ i = actOn (· ≠ i)
(V₀ i V₀ iᵀ)` and `P₁ i = modeProj i (U₁ i)`: orthogonality and commutation of the projectors
are derived, not assumed. This is `Tensor.isTuckerBUGStep_of_orthonormal` without the normal
bound. -/
theorem isTuckerBUGStepCore_of_orthonormal {r s : Fin d → Type*} [∀ i, Fintype (r i)]
    [∀ i, DecidableEq (r i)] [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)]
    {U₁ : ∀ i, Matrix (ι i) (r i) ℝ} (hU₁ : ∀ i, (U₁ i)ᵀ * U₁ i = 1)
    {V₀ : ∀ i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (s i) ℝ}
    (hV₀ : ∀ i, (V₀ i)ᵀ * V₀ i = 1) {F : ℝ → Tensor ι → Tensor ι} {t₀ t₁ : ℝ}
    {Y₀ : Tensor ι} {YK : Fin d → ℝ → Tensor ι} {YS : ℝ → Tensor ι}
    (hK : ∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (YK i) t₀ t₁)
    (hK₀ : ∀ i, YK i t₀ = Y₀) (hcap : ∀ i, modeProj i (U₁ i) (YK i t₁) = YK i t₁)
    (hS : ODESolution (fun t x => modeProd (fun i => modeProj i (U₁ i)) (F t x)) YS t₀ t₁)
    (hS₀ : YS t₀ = modeProd (fun i => modeProj i (U₁ i)) Y₀) :
    IsTuckerBUGStepCore F (fun i => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ))
      (fun i => modeProj i (U₁ i)) t₀ t₁ Y₀ YK YS :=
  ⟨⟨fun i => isOrthProj_coRangeProj i (hV₀ i), fun i => isOrthProj_modeProj i (hU₁ i),
    modeProj_comm_family U₁, hK, hK₀, hcap⟩, hS, hS₀⟩

end Tensor

namespace TuckerBUG

open Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)]

/-! ### The step relation and the normal triples -/

section Rel

/-- **The Tucker BUG step with multilinear rank `r`, as a relation between tensors**
(arXiv:2010.02022, §5.1). `stepRel F r t₀ t₁ Y₀ Y₁` holds if there are co-range bases `V₀ i`
with `r i` orthonormal columns whose projectors fix `Y₀`, mode bases `U₁ i` with `r i`
orthonormal columns, K-step trajectories `YK i` (solutions of `Ẏ = Q₀ i F(t, Y)` from `Y₀`, with
`Q₀ i = actOn (· ≠ i) (V₀ i V₀ iᵀ)`) whose results are fixed by the new mode projectors
`modeProj i (U₁ i)`, and a Galerkin trajectory `YS` (a solution of `Ẏ = Π F(t, Y)` from `Π Y₀`,
with `Π` the product of the new mode projectors) with `Y₁ = YS t₁`. -/
def stepRel (F : ℝ → Tensor ι → Tensor ι) (r : Fin d → ℕ) : StepRel (Tensor ι) :=
  fun t₀ t₁ Y₀ Y₁ =>
    ∃ (V₀ : ∀ i, Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin (r i)) ℝ)
      (U₁ : ∀ i, Matrix (ι i) (Fin (r i)) ℝ) (YK : Fin d → ℝ → Tensor ι) (YS : ℝ → Tensor ι),
      (∀ i, (V₀ i)ᵀ * V₀ i = 1) ∧ (∀ i, actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) Y₀ = Y₀) ∧
      (∀ i, (U₁ i)ᵀ * U₁ i = 1) ∧
      (∀ i, ODESolution (fun t x => actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (F t x)) (YK i) t₀ t₁) ∧
      (∀ i, YK i t₀ = Y₀) ∧ (∀ i, modeProj i (U₁ i) (YK i t₁) = YK i t₁) ∧
      ODESolution (fun t x => modeProd (fun i => modeProj i (U₁ i)) (F t x)) YS t₀ t₁ ∧
      YS t₀ = modeProd (fun i => modeProj i (U₁ i)) Y₀ ∧ Y₁ = YS t₁

/-- The triples (new mode projector, old co-range projector, tensor) at which the Tucker BUG step
evaluates the normal part of the field: for some mode `i`, `U` with `r i` orthonormal columns,
`V` with `r i` orthonormal columns indexed by the multi-indices of the other modes, and a tensor
fixed by both projectors. -/
def normalTriples (r : Fin d → ℕ) :
    Set ((Tensor ι →L[ℝ] Tensor ι) × (Tensor ι →L[ℝ] Tensor ι) × Tensor ι) :=
  {T | ∃ (i : Fin d) (U : Matrix (ι i) (Fin (r i)) ℝ)
    (V : Matrix (∀ k : {k : Fin d // k ≠ i}, ι k) (Fin (r i)) ℝ) (Y : Tensor ι),
    Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ modeProj i U Y = Y ∧ actOn (· ≠ i) (V * Vᵀ) Y = Y ∧
      T = (modeProj i U, actOn (· ≠ i) (V * Vᵀ), Y)}

variable {F : ℝ → Tensor ι → Tensor ι} {r : Fin d → ℕ} {t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι}

/-- **Invariance: the result of a step has multilinear rank at most `r`.** The Galerkin step
starts in the range of the product `Π` of the new mode projectors and stays there
(`ODESolution.galerkin_mem_range`), and each new mode projector fixes the range of `Π`. -/
theorem stepRel.modeRankLE (h : stepRel F r t₀ t₁ Y₀ Y₁) (h01 : t₀ ≤ t₁) :
    ModeRankLE r Y₁ := by
  obtain ⟨V₀, U₁, YK, YS, -, -, hU₁, -, -, -, hS, hS₀, rfl⟩ := h
  have hP := isOrthProj_modeProd_modeProj hU₁
  have hinv := hS.galerkin_mem_range hP (by rw [hS₀]; exact hP.idem _) t₁ ⟨h01, le_rfl⟩
  intro i
  refine ⟨U₁ i, hU₁ i, ?_⟩
  rw [← hinv]
  exact apply_modeProd_eq_self (fun j x => (isOrthProj_modeProj j (hU₁ j)).idem x)
    (modeProj_comm_family U₁) i _

end Rel

/-! ### Near a reference solution: locality and local error -/

section Tube

variable {F : ℝ → Tensor ι → Tensor ι} {r : Fin d → ℕ} {t₀ t₁ : ℝ} {Y₀ Y₁ : Tensor ι}
  {A : ℝ → Tensor ι} {a b ρ B : ℝ}

/-- **Near the reference solution, the tube extension has the same Tucker BUG steps as the
field.** Let `F` be bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`,
and let `[t₀, t₁] ⊆ [a, b]`. If `‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, the relation `stepRel`
is the same for `tubeExt F A a b ρ` and for `F` (`isTuckerBUGStepCore_tubeExt_iff_of_near`). -/
theorem stepRel_tubeExt_iff_of_near (hFB : IsBoundedOnTube F A a b ρ B) (hB : 0 ≤ B)
    (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hA : ODESolution F A t₀ t₁)
    (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    stepRel (tubeExt F A a b ρ) r t₀ t₁ Y₀ Y₁ ↔ stepRel F r t₀ t₁ Y₀ Y₁ := by
  constructor
  · rintro ⟨V₀, U₁, YK, YS, hV₀, hY₀, hU₁, hK, hK₀, hcap, hS, hS₀, rfl⟩
    have hs := (isTuckerBUGStepCore_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).1
      (isTuckerBUGStepCore_of_orthonormal hU₁ hV₀ hK hK₀ hcap hS hS₀)
    exact ⟨V₀, U₁, YK, YS, hV₀, hY₀, hU₁, hs.kSol, hK₀, hcap, hs.sSol, hS₀, rfl⟩
  · rintro ⟨V₀, U₁, YK, YS, hV₀, hY₀, hU₁, hK, hK₀, hcap, hS, hS₀, rfl⟩
    have hs := (isTuckerBUGStepCore_tubeExt_iff_of_near hFB hB ha hb h01 hA hsmall).2
      (isTuckerBUGStepCore_of_orthonormal hU₁ hV₀ hK hK₀ hcap hS hS₀)
    exact ⟨V₀, U₁, YK, YS, hV₀, hY₀, hU₁, hs.kSol, hK₀, hcap, hs.sSol, hS₀, rfl⟩

/-- **Local error of the Tucker BUG step near a reference solution.** Let `F` be `L`-Lipschitz
and bounded by `B` on the tube of radius `ρ` around a solution `A` over `[a, b]`, and let the
normal part of `F` be at most `ε` at the triples `TuckerBUG.normalTriples r` of this tube. If the
step over `[t₀, t₁] ⊆ [a, b]` has size `t₁ - t₀ ≤ H` and its start value satisfies
`‖Y₀ - A t₀‖ + (d + 2) B (t₁ - t₀) < ρ`, then every step of `TuckerBUG.stepRel F r` from `Y₀`
has local error at most `(t₁ - t₀) (c₁ ε + c₂ (t₁ - t₀))` with `c₁ = tuckerC₁ d L H` and
`c₂ = tuckerC₂ d L B H` (arXiv:2010.02022, Lemma 7, for a field that is Lipschitz and bounded
near the reference solution only). The normal part is evaluated at the results `YK i t₁` of the
K-steps, which lie in the tube and are fixed by the new mode projector and by the old co-range
projector, so that `(P₁ i, Q₀ i, YK i t₁)` is a normal triple. -/
theorem stepRel.hasLocalError_of_tube {L ε H : ℝ} (h : stepRel F r t₀ t₁ Y₀ Y₁)
    (hε : NormalBoundOn F (normalTriples r) (tubeSet A a b ρ) ε)
    (hFL : IsLipschitzOnTube F A a b ρ L) (hL : 0 ≤ L) (hFB : IsBoundedOnTube F A a b ρ B)
    (hB : 0 ≤ B) (ha : a ≤ t₀) (hb : t₁ ≤ b) (h01 : t₀ ≤ t₁) (hH : t₁ - t₀ ≤ H)
    (hA : ODESolution F A t₀ t₁) (hsmall : ‖Y₀ - A t₀‖ + (d + 2) * B * (t₁ - t₀) < ρ) :
    HasLocalError F t₀ t₁ Y₀ Y₁
      ((t₁ - t₀) * (tuckerC₁ d L H * ε + tuckerC₂ d L B H * (t₁ - t₀))) := by
  obtain ⟨V₀, U₁, YK, YS, hV₀, hY₀, hU₁, hK, hK₀, hcap, hS, hS₀, rfl⟩ := h
  have hs := isTuckerBUGStepCore_of_orthonormal hU₁ hV₀ hK hK₀ hcap hS hS₀
  have hBh : 0 ≤ B * (t₁ - t₀) := mul_nonneg hB (sub_nonneg.2 h01)
  have hdBh : 0 ≤ (d : ℝ) * (B * (t₁ - t₀)) := mul_nonneg (Nat.cast_nonneg d) hBh
  have h2 : ‖Y₀ - A t₀‖ + 2 * B * (t₁ - t₀) < ρ := by linarith
  have hmem := hs.toBasisUpdate.mem_tubeSet_of_near hFB hB ha hb h01 hA h2
  refine hs.hasLocalError_of_tube (fun i t ht => ?_) hFL hL hFB hB ha hb h01 hH hA hsmall
  -- the result of the K-step stays in the range of the co-range projector
  have hQ : actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ) (YK i t₁) = YK i t₁ :=
    (hK i).galerkin_mem_range (isOrthProj_coRangeProj i (hV₀ i)) (by rw [hK₀ i]; exact hY₀ i)
      t₁ ⟨h01, le_rfl⟩
  exact hε t (modeProj i (U₁ i)) (actOn (· ≠ i) (V₀ i * (V₀ i)ᵀ)) (YK i t₁)
    ⟨i, U₁ i, V₀ i, YK i t₁, hU₁ i, hV₀ i, hcap i, hQ, rfl⟩ (hmem i t ht)

end Tube

/-! ### Examples -/

section Examples

/-- **Non-vacuity of `TuckerBUG.normalTriples`.** For tensors whose modes have one index each,
every tensor `Y` (for instance a nonzero one) gives a normal triple with the mode basis `1` and
the co-range basis whose single entry is `1`, for multilinear rank `1`. -/
example {d : ℕ} (i : Fin d) (Y : Tensor fun _ : Fin d => Fin 1)
    (V : Matrix ({k : Fin d // k ≠ i} → Fin 1) (Fin 1) ℝ) (hV : ∀ a b, V a b = 1) :
    (modeProj i (1 : Matrix (Fin 1) (Fin 1) ℝ), actOn (· ≠ i) (V * Vᵀ), Y) ∈
      normalTriples (ι := fun _ : Fin d => Fin 1) (fun _ => 1) := by
  -- the co-range projector fixes `Y`: the sum over the single multi-index of the other modes
  have hQ : actOn (· ≠ i) (V * Vᵀ) Y = Y := by
    ext x
    simp only [actOn_apply]
    rw [Finset.sum_eq_single (Subtype.restrict (· ≠ i) x)
      (fun z _ hz => (hz (Subsingleton.elim z _)).elim) (fun h => (h (Finset.mem_univ _)).elim),
      override_restrict]
    simp [Matrix.mul_apply, hV]
  refine ⟨i, 1, V, Y, by simp, ?_, by simp [modeProj], hQ, rfl⟩
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, hV, Subsingleton.elim a b]

end Examples

end TuckerBUG

end LeanDLRA

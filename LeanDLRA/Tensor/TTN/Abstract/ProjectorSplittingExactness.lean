import LeanDLRA.Tensor.TTN.Abstract.ProjectorSplitting

/-!
# Exactness of the nested Tucker projector-splitting integrator

Projector level, on a real inner product space; the realization on tensors over a dimension tree
is `LeanDLRA/Tensor/TTN/ProjectorSplittingExactness.lean`. For a field `F(t, Y) = Ȧ(t)` and exact
`K`-steps (`IsExactKSteps`), the values of a step of the nested Tucker projector-splitting
integrator (`IsTuckerKSLStep`) are explicit, and the step reproduces `A t₁` when `A t₁` is
recoverable from each of its `K`-step projections.

## Main results

* `tucker_ksl_explicit`: the `K`-values, the intermediate values and the result of a step in
  closed form.
* `tucker_ksl_exact`: the step reproduces `A t₁` [LubichVandereyckenWalach2018, Thm. 3].

## Implementation notes

The non-degeneracy condition of the paper (invertibility of `Wᵢ(t₁)ᵀ Wᵢ(t₀)`) is replaced by its
abstract form, the recoverability `Exactness.IsRecoverable` of `A t₁` for every mode.

## References

* [LubichVandereyckenWalach2018]
-/

open Set Finset
open scoped RealInnerProductSpace

namespace LeanDLRA

section Exactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem modePrefix_apply_eq_self {d k : ℕ} {P : Fin d → E →L[ℝ] E} {x : E}
    (h : ∀ j : Fin d, (j : ℕ) < k → P j x = x) : modePrefix P k x = x :=
  Exactness.list_prod_apply_eq_self fun T hT => by
    obtain ⟨j, hj, rfl⟩ := mem_take_ofFn hT
    exact h j hj

private theorem modePrefix_succ_apply {d k : ℕ} (P : Fin d → E →L[ℝ] E) (hk : k < d) (x : E) :
    modePrefix P (k + 1) x = modePrefix P k (P ⟨k, hk⟩ x) := by
  have : (List.ofFn P)[k]? = some (P ⟨k, hk⟩) := by simp [hk]
  simp only [modePrefix, List.take_add_one, this, Option.toList_some, List.prod_append,
    List.prod_singleton]
  rfl

/-- For a field `F(t, Y) = Ȧ(t)` (`IsDerivRHS`) and exact `K`-steps (`IsExactKSteps`), the values
of a step of the nested Tucker projector-splitting integrator from `A t₀` are explicit: with
`Πᵢ = modePrefix P₁ i` and `Δ = A t₁ - A t₀`, `K i = X i + Q₀ i Πᵢ Δ`,
`X (i + 1) = K i - P₁ i Q₀ i Πᵢ Δ` and `YC t₁ = X d + modeProd P₁ Δ`. -/
theorem tucker_ksl_explicit {d : ℕ} {F : ℝ → E → E} {A : ℝ → E} {ε t₀ t₁ : ℝ}
    (ht : t₀ ≤ t₁) (hA : IsDerivRHS F A t₀ t₁) {Q₀ P₁ : Fin d → E →L[ℝ] E}
    {X : Fin (d + 1) → E} {K : Fin d → E} {YS : Fin d → ℝ → E} {YC : ℝ → E}
    (hs : IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ (A t₀) X K YS YC)
    (hK : IsExactKSteps F Q₀ P₁ t₀ t₁ X K) :
    (∀ i : Fin d, K i = X i.castSucc + (Q₀ i * modePrefix P₁ (i : ℕ)) (A t₁ - A t₀)) ∧
    (∀ i : Fin d, X i.succ =
      K i + (-(P₁ i * (Q₀ i * modePrefix P₁ (i : ℕ)))) (A t₁ - A t₀)) ∧
    YC t₁ = X (Fin.last d) + (modeProd P₁) (A t₁ - A t₀) := by
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · obtain ⟨y, hy, hy0, hy1⟩ := hK i
    have := hy.eq_add_map_sub (Q₀ i * modePrefix P₁ (i : ℕ)) (A := A) (A' := fun t => F t (y t))
      hA.cont (fun t ht => hA.deriv t ht (y t)) (fun t _ => rfl) t₁ ⟨ht, le_rfl⟩
    rw [← hy1, this, hy0]
  · have := (hs.sSol i).eq_add_map_sub (-(P₁ i * (Q₀ i * modePrefix P₁ (i : ℕ)))) (A := A)
      (A' := fun t => F t (YS i t)) hA.cont (fun t ht => hA.deriv t ht (YS i t))
      (fun t _ => by simp) t₁ ⟨ht, le_rfl⟩
    rw [hs.next i, this, hs.sStart i]
  · have := hs.cSol.eq_add_map_sub (modeProd P₁) (A := A) (A' := fun t => F t (YC t))
      hA.cont (fun t ht => hA.deriv t ht (YC t)) (fun t _ => rfl) t₁ ⟨ht, le_rfl⟩
    rw [this, hs.cStart]

/-- **Exactness of the nested Tucker projector-splitting integrator.** For `F(t, Y) = Ȧ(t)`
(`IsDerivRHS`), a step from `A t₀` with exact `K`-steps (`IsExactKSteps`) gives `YC t₁ = A t₁`
if, for every mode `i`, `A t₁` is recoverable from its `K`-step projection `Q₀ i (A t₁)` modulo a
class `𝓛 i ∋ P₁ i` of mode-`i` operators (`Exactness.IsRecoverable`, the abstract form of the
invertibility of `Wᵢ(t₁)ᵀ Wᵢ(t₀)`) [LubichVandereyckenWalach2018, Thm. 3]. The recoverability is
assumed for every mode `i`. -/
theorem tucker_ksl_exact {d : ℕ} {F : ℝ → E → E} {A : ℝ → E} {ε t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) {Q₀ P₁ : Fin d → E →L[ℝ] E} {X : Fin (d + 1) → E}
    {K : Fin d → E} {YS : Fin d → ℝ → E} {YC : ℝ → E}
    (hs : IsTuckerKSLStep F ε Q₀ P₁ t₀ t₁ (A t₀) X K YS YC)
    (hK : IsExactKSteps F Q₀ P₁ t₀ t₁ X K) {𝓛 : Fin d → Set (E →L[ℝ] E)}
    (h𝓛 : ∀ i, P₁ i ∈ 𝓛 i) (hrec : ∀ i, Exactness.IsRecoverable (𝓛 i) (Q₀ i) (A t₁)) :
    YC t₁ = A t₁ := by
  have hm : ∀ (S T : E →L[ℝ] E) (x : E), (S * T) x = S (T x) := fun _ _ _ => rfl
  have hKeq : ∀ i : Fin d, K i = X i.castSucc + (Q₀ i * modePrefix P₁ (i : ℕ)) (A t₁ - A t₀) := by
    intro i
    obtain ⟨y, hy, hy0, hy1⟩ := hK i
    have := hy.eq_add_map_sub (Q₀ i * modePrefix P₁ (i : ℕ)) (A := A) (A' := fun t => F t (y t))
      hA.cont (fun t ht => hA.deriv t ht (y t)) (fun t _ => rfl) t₁ ⟨ht, le_rfl⟩
    rw [← hy1, this, hy0]
  have hSeq : ∀ i : Fin d, X i.succ =
      K i + (-(P₁ i * (Q₀ i * modePrefix P₁ (i : ℕ)))) (A t₁ - A t₀) := by
    intro i
    have := (hs.sSol i).eq_add_map_sub (-(P₁ i * (Q₀ i * modePrefix P₁ (i : ℕ)))) (A := A)
      (A' := fun t => F t (YS i t)) hA.cont (fun t ht => hA.deriv t ht (YS i t))
      (fun t _ => by simp) t₁ ⟨ht, le_rfl⟩
    rw [hs.next i, this, hs.sStart i]
  have key : ∀ k, (hk : k ≤ d) → X ⟨k, Nat.lt_succ_of_le hk⟩ = modePrefix P₁ k (A t₀) ∧
      ∀ j : Fin d, (j : ℕ) < k → P₁ j (A t₁) = A t₁ := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      simpa using hs.start
    | succ k ih =>
      intro hk
      obtain ⟨hX, hfix⟩ := ih (by omega)
      set i : Fin d := ⟨k, by omega⟩ with hi
      have hik : (i : ℕ) = k := rfl
      have hPi : modePrefix P₁ k (A t₁) = A t₁ := modePrefix_apply_eq_self hfix
      have hXi : X i.castSucc = modePrefix P₁ k (A t₀) := hX
      have hQ : Q₀ i (modePrefix P₁ k (A t₀)) = modePrefix P₁ k (A t₀) := by
        rw [← hXi]; exact hs.qFix i
      have hKi : K i = Q₀ i (A t₁) := by
        rw [hKeq i, hXi]
        simp only [hm, map_sub, hik, hPi, hQ]
        abel
      have hPa : P₁ i (A t₁) = A t₁ :=
        Exactness.apply_eq_self_of_isRecoverable (h𝓛 i) (by rw [← hKi]; exact hs.kCap i) (hrec i)
      refine ⟨?_, ?_⟩
      · have h1 : X i.succ = P₁ i (X i.castSucc) := by
          have e1 := hSeq i
          have e2 : (Q₀ i * modePrefix P₁ (i : ℕ)) (A t₁ - A t₀) = K i - X i.castSucc := by
            rw [hKeq i]; abel
          have e3 : (-(P₁ i * (Q₀ i * modePrefix P₁ (i : ℕ)))) (A t₁ - A t₀) =
              -(P₁ i (K i - X i.castSucc)) := by
            rw [← e2]; rfl
          rw [e1, e3, map_sub, hs.kCap i]
          abel
        change X i.succ = _
        rw [h1, hXi, modePrefix_succ_apply P₁ (by omega), modePrefix_comm hs.comm₁]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact hfix j h
        · have : j = i := Fin.ext h
          rw [this]; exact hPa
  obtain ⟨hXd, hfixd⟩ := key d le_rfl
  have hall : modePrefix P₁ d (A t₁) = A t₁ := modePrefix_apply_eq_self hfixd
  have hc := hs.cSol
  have hcA := hc.eq_add_map_sub (modeProd P₁) (A := A) (A' := fun t => F t (YC t))
    hA.cont (fun t ht => hA.deriv t ht (YC t)) (fun t _ => rfl) t₁ ⟨ht, le_rfl⟩
  rw [hcA, hs.cStart, map_sub, ← modePrefix_of_le P₁ (le_refl d)]
  have : X (Fin.last d) = modePrefix P₁ d (A t₀) := hXd
  rw [this, hall]
  abel

end Exactness

end LeanDLRA

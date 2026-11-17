import LeanDLRA.Tensor.TT.ProjectorSplitting
import LeanDLRA.Integrators.Exactness

/-!
# Exactness of the tensor-train projector-splitting integrator

For a state-independent right-hand side `F(t, Y) = Ȧ(t)` every substep of the tensor-train (TT)
projector-splitting integrator `IsTTKSLStep` is an explicit increment (Lubich–Oseledets–
Vandereycken [LubichOseledetsVandereycken2015], Theorem 4.1), and the signed substep projectors
add up to the TT tangent projector. Hence one step returns
`Y₁ = Y₀ + P (A(t₁) - A(t₀))` with `P = ttTangentProj U V` built from the new left-orthogonal
cores `U` and the old right-orthogonal cores `V`, without any rank condition.

If moreover `Y₀ = A(t₀)` and `A(t₁)` satisfies a non-degeneracy condition at every inner bond,
the step is exact, `Y₁ = A(t₁)` ([LubichOseledetsVandereycken2015], Theorem 5.1 for the
first-order sweep, proved through Lemma 5.2). As in the matrix and tree tensor network cases of
the library (`Exactness.IsRecoverable`, `DimTree.IsNondegenerateProjectorSplittingStep`), the
condition is stated in the abstract form "`A(t₁)` is recoverable from `P_{>k} A(t₁)` modulo the
operators acting on the modes `< k`"; `isRecoverable_ttRightProj_of_isUnit` derives it from the
hypothesis of the paper, a factorization `A(t₁)⟨k⟩ = U S Wᵀ` of the `k`-th unfolding whose right
factor has an invertible overlap `Wᵀ X_{>k}` with the right interface of the old cores (the
paper's `Q_{≥k}(t₁)ᵀ Q_{≥k}(t₀)`, invertible for `t₁ - t₀` small).

## Main results

* `IsTTKSLStep.eq_add_ttTangentProj`: `Y₁ = Y₀ + ttTangentProj U V (A t₁ - A t₀)` for every
  state-independent field.
* `IsTTKSLStep.ttRightProj_start`: the start value is fixed by every right interface projector.
* `IsTTKSLStep.kStep_eq_ttRightProj`, `IsTTKSLStep.sStep_eq_ttLeftProj`: the two identities of
  [LubichOseledetsVandereycken2015], Lemma 5.2, `YK k t₁ = P_{>k+1} A(t₁)` and
  `YS k t₁ = P_{≤k+1} A(t₀)`.
* `IsTTKSLStep.exact`: **exactness** ([LubichOseledetsVandereycken2015], Theorem 5.1).
* `isRecoverable_ttRightProj_of_isUnit`, `IsTTKSLStep.exact_of_isUnit`: the non-degeneracy
  condition from the invertible overlaps of the paper, and exactness in this form.
* `TTKSLExample`: a step on `ℝ² ⊗ ℝ² ⊗ ℝ²` with bond dimension one. The curve
  `A(t) = e₀ ⊗ e₀ ⊗ e₀ + t c`, `c = (2, 4) ⊗ e₀ ⊗ e₀`, turns its first factor from `e₀` to
  `(3, 4)`; the step from `A(0)` with the old cores `e₀, e₀, e₀` has the new cores `u, e₀, e₀`,
  `u = (3/5, 4/5)`; its backward substeps end at `(3/5) u ⊗ e₀ ⊗ e₀`, off the curve. The interface
  projectors of elementary tensor trains are computed in `ttLeftProj_vcores` and
  `ttRightProj_vcores`. The examples of this file and of
  `Tensor/TT/ProjectorSplittingError.lean` (with the field `c + n`, `n` doubly normal) use it.

## Implementation notes

Only the final value `A(t₁)` enters the non-degeneracy condition, and only the right overlaps
are used: the paper also needs the left overlaps `Q_{≤k}(t₁)ᵀ Q_{≤k}(t₀)` to identify the
substep projectors with tangent projectors of intermediate tensor trains, which the step
relation `IsTTKSLStep` gives directly. The middle factor `S` may be singular (TT ranks at most the
bond dimensions). The second-order (forward and backward) sweep is not treated.

## References

* [LubichOseledetsVandereycken2015]
-/

open Set
open scoped Matrix

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]
  [∀ k, DecidableEq (β k)]

/-- Acting on the modes outside `p` is right multiplication of the `p`-unfolding by the
transposed matrix. -/
private lemma unfold_actOn_not {κ : Type*} [Fintype κ] [DecidableEq κ] {ι : κ → Type*}
    [∀ k, Fintype (ι k)] (p : κ → Prop) [DecidablePred p]
    (N : Matrix (∀ k : {k // ¬ p k}, ι k) (∀ k : {k // ¬ p k}, ι k) ℝ) (Y : Tensor ι) :
    unfold p (actOn (fun k => ¬ p k) N Y) = unfold p Y * Nᵀ := by
  ext a b
  simp only [unfold_apply, actOn_apply, Matrix.mul_apply, Matrix.transpose_apply,
    restrict_not_merge]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : override (fun k => ¬ p k) (merge p a b) z = merge p a z := by
    funext k
    by_cases h : p k <;> simp [override, merge, h]
  rw [hz, mul_comm]

/-- **Non-degeneracy from an invertible overlap** ([LubichOseledetsVandereycken2015], proof of
Lemma 5.2). Let the cores `k, …, d - 1` of `V` be right-orthogonal and let the `k`-th unfolding
of `Z` factor as `Z⟨k⟩ = U S Wᵀ` (rank at most the bond dimension; `S` may be singular) with
`Wᵀ X_{>k}` invertible, where `X_{>k} = ttRight V k` is the right interface of `V`. Then `Z` is
recoverable from `P_{>k} Z` modulo the operators acting on the modes `< k`. -/
theorem isRecoverable_ttRightProj_of_isUnit [Subsingleton (β d)] {V : TTCores ι β} {k : ℕ}
    (hk : k ≤ d) (hV : ∀ i : Fin d, k ≤ i.val → IsRightOrth V i) {Z : Tensor ι}
    {U : Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ} {S : Matrix (β k) (β k) ℝ}
    {W : Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ}
    (hZ : unfold (fun i : Fin d => i.val < k) Z = U * S * Wᵀ)
    (hW : IsUnit (Wᵀ * ttRight V k)) :
    Exactness.IsRecoverable (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k))
      (ttRightProj V k) Z := by
  obtain ⟨C, hC⟩ := Exactness.exists_eq_mul_mul_of_isUnit hZ hW
  have hX : (ttRight V k)ᵀ * ttRight V k = 1 := ttRight_transpose_mul_self k hk hV
  refine ⟨actOn (fun i : Fin d => ¬ i.val < k) (Cᵀ * (ttRight V k)ᵀ), ?_, ?_⟩
  · rintro _ ⟨M, rfl⟩ y
    exact actOn_comm_of_disjoint _ (fun i h1 h2 => h2 h1) M _ y
  · refine unfold_injective (fun i : Fin d => i.val < k) ?_
    rw [unfold_actOn_not, ttRightProj, unfold_actOn_not]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc unfold (fun i : Fin d => i.val < k) Z * (ttRight V k * (ttRight V k)ᵀ) *
          (ttRight V k * C)
        = unfold (fun i : Fin d => i.val < k) Z * ttRight V k *
            ((ttRight V k)ᵀ * ttRight V k * C) := by
          simp only [Matrix.mul_assoc]
      _ = unfold (fun i : Fin d => i.val < k) Z := by rw [hX, Matrix.one_mul, ← hC]

namespace IsTTKSLStep

variable {F : ℝ → Tensor ι → Tensor ι} {U V : TTCores ι β} {t₀ t₁ : ℝ} {Y₀ : Tensor ι}
  {YK YS : ℕ → ℝ → Tensor ι} {A : ℝ → Tensor ι}

/-- The partial sweeps for a state-independent field: after the forward substep of core `k`,
`YK k t₁ = Y₀ + (∑_{j ≤ k} P_{≤j} P_{>j+1} - ∑_{j < k} P_{≤j+1} P_{>j+1}) (A t₁ - A t₀)`. -/
private lemma kStep_eq_add_sum (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) :
    ∀ k < d, YK k t₁ = Y₀ + (∑ j ∈ Finset.range (k + 1), ttKProj U V j -
      ∑ j ∈ Finset.range k, ttSProj U V j) (A t₁ - A t₀) := by
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  intro k hk
  induction k with
  | zero =>
    rw [Exactness.galerkin_eq_add hA (ttKProj U V 0) (fun _ _ => rfl) (hs.kSol 0 hk) t₁ h1,
      hs.kStart₀]
    simp
  | succ k ih =>
    have hk' : k + 1 < d := hk
    rw [Exactness.galerkin_eq_add hA (ttKProj U V (k + 1)) (fun _ _ => rfl)
        (hs.kSol (k + 1) hk) t₁ h1, hs.kStart k hk',
      Exactness.galerkin_eq_add hA (-ttSProj U V k) (fun _ _ => rfl) (hs.sSol k hk') t₁ h1,
      hs.sStart k hk', ih (by omega), Finset.sum_range_succ (fun j => ttKProj U V j) (k + 1),
      Finset.sum_range_succ (fun j => ttSProj U V j) k]
    simp only [_root_.sub_apply, _root_.add_apply,
      _root_.neg_apply]
    abel

/-- **The TT projector-splitting step for a state-independent field**
([LubichOseledetsVandereycken2015], Theorem 4.1 for the substeps): if `F(t, Y) = Ȧ(t)` on
`[t₀, t₁]`, one step from an arbitrary `Y₀` returns `Y₀ + P (A(t₁) - A(t₀))`, where
`P = ttTangentProj U V` is the alternating sum of the substep projectors. No rank condition is
needed. -/
theorem eq_add_ttTangentProj (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hd : 0 < d) :
    YK (d - 1) t₁ = Y₀ + ttTangentProj U V (A t₁ - A t₀) := by
  have h := kStep_eq_add_sum hs ht hA (d - 1) (by omega)
  rwa [Nat.sub_add_cancel hd, ← ttTangentProj_eq_sum_substeps] at h

/-- The start value of a step is fixed by every right interface projector `P_{>j}`, `1 ≤ j ≤ d`
(nested right interfaces). -/
theorem ttRightProj_start [Subsingleton (β d)] (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) :
    ∀ j, 0 < j → j ≤ d → ttRightProj V j Y₀ = Y₀ := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ j ih =>
    intro _ hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hs.start
    · have h := congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T Y₀)
        (ttRightProj_succ_mul (B := V) (k := j) (by omega)
          fun i hi => hs.rightOrth i (by omega))
      simp only [mul_apply_eq_comp] at h
      rw [ih hj0 (by omega)] at h
      exact h

variable [Unique (β 0)] [Unique (β d)]

/-- **The forward substeps for a recoverable target** ([LubichOseledetsVandereycken2015],
Lemma 5.2, first identity): if `F(t, Y) = Ȧ(t)`, `Y₀ = A(t₀)` and `A(t₁)` is recoverable from
`P_{>k+1} A(t₁)` modulo the operators on the modes `≤ k` at every inner bond, then the forward
substep of core `k` ends at `YK k t₁ = P_{>k+1} A(t₁)`. -/
theorem kStep_eq_ttRightProj (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hrec : ∀ k, k + 1 < d → Exactness.IsRecoverable
      (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1)) (ttRightProj V (k + 1))
      (A t₁)) :
    ∀ k < d, YK k t₁ = ttRightProj V (k + 1) (A t₁) := by
  have hR : ∀ j, 0 < j → j ≤ d → ttRightProj V j (A t₀) = A t₀ := fun j h0 hj =>
    hY₀ ▸ hs.ttRightProj_start j h0 hj
  have h1 : t₁ ∈ Icc t₀ t₁ := ⟨ht, le_rfl⟩
  intro k hk
  induction k with
  | zero =>
    rw [Exactness.galerkin_eq_add hA (ttKProj U V 0) (fun _ _ => rfl) (hs.kSol 0 hk) t₁ h1,
      hs.kStart₀, hY₀]
    simp only [ttKProj, mul_apply_eq_comp, ttLeftProj_zero,
      one_apply_eq_self, map_sub, hR 1 one_pos (by omega)]
    abel
  | succ k ih =>
    have hk' : k + 1 < d := hk
    have hK := ih (by omega)
    have hcap : ttLeftProj U (k + 1) (A t₁) = A t₁ := by
      refine Exactness.apply_eq_self_of_isRecoverable
        (𝓛 := Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1))
        ⟨ttLeft U (k + 1) * (ttLeft U (k + 1))ᵀ, rfl⟩ ?_ (hrec k hk')
      rw [← hK]
      exact hs.kCap k hk'
    have hc1 : ∀ x, ttLeftProj U (k + 1) (ttRightProj V (k + 1) x) =
        ttRightProj V (k + 1) (ttLeftProj U (k + 1) x) := fun x =>
      congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T x) (ttLeftProj_comm_ttRightProj U V le_rfl)
    have hc2 : ∀ x, ttLeftProj U (k + 1) (ttRightProj V (k + 1 + 1) x) =
        ttRightProj V (k + 1 + 1) (ttLeftProj U (k + 1) x) := fun x =>
      congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T x)
        (ttLeftProj_comm_ttRightProj U V (Nat.le_succ _))
    rw [Exactness.galerkin_eq_add hA (ttKProj U V (k + 1)) (fun _ _ => rfl)
        (hs.kSol (k + 1) hk) t₁ h1, hs.kStart k hk',
      Exactness.galerkin_eq_add hA (-ttSProj U V k) (fun _ _ => rfl) (hs.sSol k hk') t₁ h1,
      hs.sStart k hk', hK]
    simp only [ttKProj, ttSProj, mul_apply_eq_comp, _root_.neg_apply,
      map_sub, hR (k + 1) (Nat.succ_pos k) hk'.le, hR (k + 1 + 1) (Nat.succ_pos _) hk, hc1, hc2,
      hcap]
    abel

/-- The new left interfaces capture the target: `P_{≤k+1} A(t₁) = A(t₁)` at every inner bond
(the capture argument in the proof of [LubichOseledetsVandereycken2015], Lemma 5.2). -/
private lemma ttLeftProj_target (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hrec : ∀ k, k + 1 < d → Exactness.IsRecoverable
      (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1)) (ttRightProj V (k + 1))
      (A t₁)) {k : ℕ} (hk : k + 1 < d) :
    ttLeftProj U (k + 1) (A t₁) = A t₁ := by
  refine Exactness.apply_eq_self_of_isRecoverable
    (𝓛 := Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1))
    ⟨ttLeft U (k + 1) * (ttLeft U (k + 1))ᵀ, rfl⟩ ?_ (hrec k hk)
  rw [← hs.kStep_eq_ttRightProj ht hA hY₀ hrec k (by omega)]
  exact hs.kCap k hk

/-- **The backward substeps for a recoverable target** ([LubichOseledetsVandereycken2015],
Lemma 5.2, second identity): under the hypotheses of `kStep_eq_ttRightProj`, the backward
substep of bond `k + 1` ends at `YS k t₁ = P_{≤k+1} A(t₀)`. -/
theorem sStep_eq_ttLeftProj (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hrec : ∀ k, k + 1 < d → Exactness.IsRecoverable
      (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1)) (ttRightProj V (k + 1))
      (A t₁)) :
    ∀ k, k + 1 < d → YS k t₁ = ttLeftProj U (k + 1) (A t₀) := by
  intro k hk
  have hR : ttRightProj V (k + 1) (A t₀) = A t₀ :=
    hY₀ ▸ hs.ttRightProj_start (k + 1) (Nat.succ_pos k) hk.le
  have hcap := hs.ttLeftProj_target ht hA hY₀ hrec hk
  have hc1 : ∀ x, ttLeftProj U (k + 1) (ttRightProj V (k + 1) x) =
      ttRightProj V (k + 1) (ttLeftProj U (k + 1) x) := fun x =>
    congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T x) (ttLeftProj_comm_ttRightProj U V le_rfl)
  rw [Exactness.galerkin_eq_add hA (-ttSProj U V k) (fun _ _ => rfl) (hs.sSol k hk) t₁
      ⟨ht, le_rfl⟩, hs.sStart k hk, hs.kStep_eq_ttRightProj ht hA hY₀ hrec k (by omega)]
  simp only [ttSProj, mul_apply_eq_comp, _root_.neg_apply, map_sub,
    hR, hc1, hcap]
  abel

/-- **Exactness of the TT projector-splitting integrator** ([LubichOseledetsVandereycken2015],
Theorem 5.1, first-order sweep). Let `F(t, Y) = Ȧ(t)` on `[t₀, t₁]` and `Y₀ = A(t₀)`. If at every
inner bond `k + 1` the target `A(t₁)` is recoverable from `P_{>k+1} A(t₁)` modulo the operators
acting on the modes `≤ k` (the non-degeneracy condition, see
`isRecoverable_ttRightProj_of_isUnit`), the step reproduces `A(t₁)` exactly. -/
theorem exact (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀)
    (hrec : ∀ k, k + 1 < d → Exactness.IsRecoverable
      (Set.range (actOn (ι := ι) fun i : Fin d => i.val < k + 1)) (ttRightProj V (k + 1))
      (A t₁)) (hd : 0 < d) :
    YK (d - 1) t₁ = A t₁ := by
  rw [hs.kStep_eq_ttRightProj ht hA hY₀ hrec (d - 1) (by omega), Nat.sub_add_cancel hd,
    ttRightProj_self, one_apply_eq_self]

/-- **Exactness of the TT projector-splitting integrator, paper form**
([LubichOseledetsVandereycken2015], Theorem 5.1 and Lemma 5.2). Let `F(t, Y) = Ȧ(t)` on
`[t₀, t₁]` and `Y₀ = A(t₀)`, and let every unfolding `A(t₁)⟨k⟩`, `0 < k < d`, factor as
`U_k S_k W_kᵀ` with `W_kᵀ X_{>k}` invertible, where `X_{>k}` is the right interface of the old
right-orthogonal cores `V`. Then the step reproduces `A(t₁)` exactly. Only the value at `t₁` and
only the right overlaps enter, and `S_k` may be singular. -/
theorem exact_of_isUnit (hs : IsTTKSLStep F U V t₀ t₁ Y₀ YK YS) (ht : t₀ ≤ t₁)
    (hA : IsDerivRHS F A t₀ t₁) (hY₀ : Y₀ = A t₀) (hd : 0 < d)
    {Uf : ∀ k, Matrix (∀ i : {i : Fin d // i.val < k}, ι i) (β k) ℝ}
    {S : ∀ k, Matrix (β k) (β k) ℝ}
    {W : ∀ k, Matrix (∀ i : {i : Fin d // ¬ i.val < k}, ι i) (β k) ℝ}
    (hZ : ∀ k, 0 < k → k < d →
      unfold (fun i : Fin d => i.val < k) (A t₁) = Uf k * S k * (W k)ᵀ)
    (hW : ∀ k, 0 < k → k < d → IsUnit ((W k)ᵀ * ttRight V k)) :
    YK (d - 1) t₁ = A t₁ :=
  hs.exact ht hA hY₀ (fun k hk => isRecoverable_ttRightProj_of_isUnit hk.le
    (fun i hi => hs.rightOrth i (by omega)) (hZ (k + 1) (Nat.succ_pos k) hk)
    (hW (k + 1) (Nat.succ_pos k) hk)) hd

end IsTTKSLStep

/-! ### Example: a rank-one curve on three modes of size two -/

namespace TTKSLExample

/-- The tensor-train cores with one-element bonds whose core `i` is the vector `v i`; the tensor
train `tt (vcores v)` is the elementary tensor `v 0 ⊗ ⋯ ⊗ v (d - 1)`. -/
def vcores (v : ∀ i, ι i → ℝ) : TTCores ι (fun _ => Unit) := fun i _ x _ => v i x

/-- The Gram entry of the left interfaces of two elementary tensor trains:
`X_{≤k}(v)ᵀ X_{≤k}(w) = ∏_{i<k} ⟨v i, w i⟩`. -/
theorem transpose_ttLeft_mul_ttLeft_apply (v w : ∀ i, ι i → ℝ) :
    ∀ k ≤ d, ∀ a b : Unit, ((ttLeft (vcores v) k)ᵀ * ttLeft (vcores w) k) a b =
      ∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), ∑ x, v i x * w i x
  | 0, _, a, b => by
    have : IsEmpty {i : Fin d // i.val < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
    rw [Matrix.mul_apply]
    change ∑ _y, (1 : ℝ) * 1 = _
    simp
  | k + 1, hk, a, b => by
    have h : k < d := hk
    have ih := transpose_ttLeft_mul_ttLeft_apply v w k h.le default default
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at ih ⊢
    rw [sum_prefixSucc k h, filter_lt_succ k h, Finset.prod_insert (not_mem_filter_lt k h), ← ih,
      Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [ttLeft_succ _ k h, restrictLE_prefixSuccEquiv_symm, prefixSuccEquiv_symm_apply_self,
      Fintype.sum_unique, vcores]
    ring

/-- The modes `≥ k` are mode `k` and the modes `≥ k + 1`. -/
private lemma filter_not_lt_eq_insert (k : ℕ) (h : k < d) :
    Finset.univ.filter (fun i : Fin d => ¬ i.val < k) =
      insert ⟨k, h⟩ (Finset.univ.filter (fun i : Fin d => ¬ i.val < k + 1)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

/-- The Gram entry of the right interfaces of two elementary tensor trains:
`X_{>k}(v)ᵀ X_{>k}(w) = ∏_{i≥k} ⟨v i, w i⟩`. -/
theorem transpose_ttRight_mul_ttRight_apply (v w : ∀ i, ι i → ℝ) (k : ℕ) (a b : Unit) :
    ((ttRight (vcores v) k)ᵀ * ttRight (vcores w) k) a b =
      ∏ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k), ∑ x, v i x * w i x := by
  induction hn : d - k generalizing k a b with
  | zero =>
    have hdk : d ≤ k := by omega
    have : IsEmpty {i : Fin d // ¬ i.val < k} := ⟨fun i => i.2 (lt_of_lt_of_le i.1.2 hdk)⟩
    rw [Matrix.mul_apply, ttRight_of_le _ k hdk, ttRight_of_le _ k hdk,
      Finset.filter_false_of_mem fun i _ => not_not.mpr (lt_of_lt_of_le i.2 hdk)]
    simp
    rfl
  | succ n ih =>
    have h : k < d := by omega
    have ih' := ih (k + 1) default default (by omega)
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at ih' ⊢
    rw [sum_suffixSucc k h, filter_not_lt_eq_insert k h, Finset.prod_insert (by simp), ← ih',
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [ttRight_of_lt _ k h, restrictLE_suffixSuccEquiv_symm,
      suffixSuccEquiv_symm_apply_self, Fintype.sum_unique, vcores]
    ring

/-- **Left interface projector of an elementary tensor train**: `P_{≤k}(u) (v 0 ⊗ ⋯ ⊗ v (d-1))`
is `∏_{i<k} ⟨u i, v i⟩` times the elementary tensor with the factors `u i`, `i < k`, and
`v i`, `i ≥ k`. -/
theorem ttLeftProj_vcores (u v : ∀ i, ι i → ℝ) {k : ℕ} (hk : k ≤ d) :
    ttLeftProj (vcores u) k (tt (vcores v)) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), ∑ x, u i x * v i x) •
        tt (vcores fun i => if i.val < k then u i else v i) := by
  have hL : ttLeft (vcores fun i => if i.val < k then u i else v i) k = ttLeft (vcores u) k :=
    ttLeft_congr k fun i hi => by funext a x b; simp [vcores, hi]
  have hR : ttRight (vcores fun i => if i.val < k then u i else v i) k = ttRight (vcores v) k :=
    ttRight_congr k fun i hi => by funext a x b; simp [vcores, not_lt.mpr hi]
  have hG : (ttLeft (vcores u) k)ᵀ * ttLeft (vcores v) k =
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), ∑ x, u i x * v i x) • 1 := by
    ext a b
    rw [transpose_ttLeft_mul_ttLeft_apply u v k hk a b]
    simp
  refine unfold_injective (fun i : Fin d => i.val < k) ?_
  rw [ttLeftProj, unfold_actOn, unfold_smul, unfold_tt _ k hk, unfold_tt _ k hk, hL, hR,
    Matrix.mul_assoc, ← Matrix.mul_assoc (ttLeft (vcores u) k)ᵀ, hG, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul]

/-- **Right interface projector of an elementary tensor train**: `P_{>k}(w) (v 0 ⊗ ⋯ ⊗ v (d-1))`
is `∏_{i≥k} ⟨v i, w i⟩` times the elementary tensor with the factors `v i`, `i < k`, and
`w i`, `i ≥ k`. -/
theorem ttRightProj_vcores (w v : ∀ i, ι i → ℝ) {k : ℕ} (hk : k ≤ d) :
    ttRightProj (vcores w) k (tt (vcores v)) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k), ∑ x, v i x * w i x) •
        tt (vcores fun i => if i.val < k then v i else w i) := by
  have hL : ttLeft (vcores fun i => if i.val < k then v i else w i) k = ttLeft (vcores v) k :=
    ttLeft_congr k fun i hi => by funext a x b; simp [vcores, hi]
  have hR : ttRight (vcores fun i => if i.val < k then v i else w i) k = ttRight (vcores w) k :=
    ttRight_congr k fun i hi => by funext a x b; simp [vcores, not_lt.mpr hi]
  have hG : (ttRight (vcores v) k)ᵀ * ttRight (vcores w) k =
      (∏ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i.val < k), ∑ x, v i x * w i x) • 1 := by
    ext a b
    rw [transpose_ttRight_mul_ttRight_apply v w k a b]
    simp
  refine unfold_injective (fun i : Fin d => i.val < k) ?_
  rw [ttRightProj, unfold_actOn_not, unfold_smul, unfold_tt _ k hk, unfold_tt _ k hk, hL, hR,
    Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.mul_assoc (ttLeft (vcores v) k), hG, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- The old cores `e₀, e₀, e₀` (`e₀ = (1, 0)`): `tt oldCores = e₀ ⊗ e₀ ⊗ e₀` is the start value. -/
noncomputable def oldCores : TTCores (fun _ : Fin 3 => Fin 2) (fun _ => Unit) :=
  vcores ![![1, 0], ![1, 0], ![1, 0]]

/-- The new cores `u, e₀, e₀` with `u = (3/5, 4/5)`. -/
noncomputable def newCores : TTCores (fun _ : Fin 3 => Fin 2) (fun _ => Unit) :=
  vcores ![![3 / 5, 4 / 5], ![1, 0], ![1, 0]]

/-- The field `c = (2, 4) ⊗ e₀ ⊗ e₀`: the curve `A(t) = e₀ ⊗ e₀ ⊗ e₀ + t c` turns its first
factor from `e₀` to `(3, 4)`. -/
noncomputable def drift : Tensor (fun _ : Fin 3 => Fin 2) :=
  tt (vcores ![![2, 4], ![1, 0], ![1, 0]])

/-- The tensor `n = u⊥ ⊗ e₁ ⊗ e₀`, `u⊥ = (-4/5, 3/5)`, `e₁ = (0, 1)`: it lies in the kernel of all
substep projectors of the example step and is doubly normal at the first inner bond. -/
noncomputable def normalDrift : Tensor (fun _ : Fin 3 => Fin 2) :=
  tt (vcores ![![-4 / 5, 3 / 5], ![0, 1], ![1, 0]])

/-- The cores `newCores` are left-orthogonal. -/
theorem isLeftOrth_newCores (i : Fin 3) : IsLeftOrth newCores i := by
  fin_cases i <;> intro b b' <;> norm_num [newCores, vcores, Fin.sum_univ_two, Matrix.one_apply]

/-- The cores `oldCores` are right-orthogonal. -/
theorem isRightOrth_oldCores (i : Fin 3) : IsRightOrth oldCores i := by
  fin_cases i <;> intro a a' <;> norm_num [oldCores, vcores, Fin.sum_univ_two, Matrix.one_apply]

/-- The right interfaces of the old and the new cores agree from the first inner bond on. -/
theorem ttRight_newCores {k : ℕ} (hk : 1 ≤ k) : ttRight newCores k = ttRight oldCores k :=
  ttRight_congr k fun i hi => by
    funext a x b
    fin_cases i
    · exfalso
      simp at hi
      omega
    · rfl
    · rfl

/-- `e₀ ⊗ e₀ ⊗ e₀ + c = 5 (u ⊗ e₀ ⊗ e₀)`. -/
theorem tt_oldCores_add_drift : tt oldCores + drift = (5 : ℝ) • tt newCores := by
  have hv : ∀ a : Fin 2, (![1, 0] : Fin 2 → ℝ) a + (![2, 4] : Fin 2 → ℝ) a =
      5 * (![3 / 5, 4 / 5] : Fin 2 → ℝ) a := by
    intro a
    fin_cases a <;> norm_num
  ext x
  rw [PiLp.add_apply, PiLp.smul_apply, drift, tt_rankOne, tt_rankOne, tt_rankOne]
  simp only [oldCores, newCores, vcores, Fin.prod_univ_three, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (hv (x 0)) * ((![1, 0] : Fin 2 → ℝ) (x 1) * (![1, 0] : Fin 2 → ℝ) (x 2))

/-- The tensor `normalDrift` is not zero. -/
theorem normalDrift_ne_zero : normalDrift ≠ 0 := by
  intro h
  have h1 : normalDrift ![0, 1, 0] = -4 / 5 := by
    rw [normalDrift, tt_rankOne]
    norm_num [vcores, Fin.prod_univ_three]
  rw [h] at h1
  norm_num at h1

/-- `P_{>1} c = c`. -/
theorem ttRightProj_one_drift : ttRightProj oldCores 1 drift = drift := by
  conv_rhs => rw [← one_smul ℝ drift]
  rw [oldCores, drift, ttRightProj_vcores _ _ (show (1 : ℕ) ≤ 3 by norm_num)]
  congr 1
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{>2} c = c`. -/
theorem ttRightProj_two_drift : ttRightProj oldCores 2 drift = drift := by
  conv_rhs => rw [← one_smul ℝ drift]
  rw [oldCores, drift, ttRightProj_vcores _ _ (show (2 : ℕ) ≤ 3 by norm_num)]
  congr 1
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{>1} n = 0`. -/
theorem ttRightProj_one_normalDrift : ttRightProj oldCores 1 normalDrift = 0 := by
  rw [oldCores, normalDrift, ttRightProj_vcores _ _ (show (1 : ℕ) ≤ 3 by norm_num), smul_eq_zero]
  left
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{>2} n = n`. -/
theorem ttRightProj_two_normalDrift : ttRightProj oldCores 2 normalDrift = normalDrift := by
  conv_rhs => rw [← one_smul ℝ normalDrift]
  rw [oldCores, normalDrift, ttRightProj_vcores _ _ (show (2 : ℕ) ≤ 3 by norm_num)]
  congr 1
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{≤1} c = ⟨u, (2, 4)⟩ U = (22/5) U` for `U = tt newCores`. -/
theorem ttLeftProj_one_drift : ttLeftProj newCores 1 drift = (22 / 5 : ℝ) • tt newCores := by
  rw [newCores, drift, ttLeftProj_vcores _ _ (show (1 : ℕ) ≤ 3 by norm_num)]
  congr 1
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{≤2} c = (22/5) U`. -/
theorem ttLeftProj_two_drift : ttLeftProj newCores 2 drift = (22 / 5 : ℝ) • tt newCores := by
  rw [newCores, drift, ttLeftProj_vcores _ _ (show (2 : ℕ) ≤ 3 by norm_num)]
  congr 1
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{≤1} n = 0`. -/
theorem ttLeftProj_one_normalDrift : ttLeftProj newCores 1 normalDrift = 0 := by
  rw [newCores, normalDrift, ttLeftProj_vcores _ _ (show (1 : ℕ) ≤ 3 by norm_num), smul_eq_zero]
  left
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- `P_{≤2} n = 0`. -/
theorem ttLeftProj_two_normalDrift : ttLeftProj newCores 2 normalDrift = 0 := by
  rw [newCores, normalDrift, ttLeftProj_vcores _ _ (show (2 : ℕ) ≤ 3 by norm_num), smul_eq_zero]
  left
  norm_num [Finset.prod_filter, Fin.prod_univ_three, Fin.sum_univ_two]

/-- The forward substeps of the example step: `YK 0 t = A(t) = e₀ ⊗ e₀ ⊗ e₀ + t c`, and for the
cores `k ≥ 1` `YK k t = (3/5 + 22 t/5) U` with `U = u ⊗ e₀ ⊗ e₀`. -/
noncomputable def kPath (k : ℕ) (t : ℝ) : Tensor (fun _ : Fin 3 => Fin 2) :=
  if k = 0 then tt oldCores + t • drift
  else (3 / 5 : ℝ) • tt newCores + t • ((22 / 5 : ℝ) • tt newCores)

/-- The backward substeps of the example step: `YS k t = (5 - 22 t/5) U`. -/
noncomputable def sPath (_k : ℕ) (t : ℝ) : Tensor (fun _ : Fin 3 => Fin 2) :=
  (5 : ℝ) • tt newCores + t • -((22 / 5 : ℝ) • tt newCores)

/-- **A TT projector-splitting step on `ℝ² ⊗ ℝ² ⊗ ℝ²`** from `e₀ ⊗ e₀ ⊗ e₀` over `[0, 1]`, with
the old cores `e₀, e₀, e₀`, the new cores `u, e₀, e₀` and the substeps `kPath`, `sPath`, for
every constant field `g` whose substep projections are those of `c`: the forward substep of
core `0` moves along `P_{>1} g = c` to `5 U`, the QR step turns the first core to `u`, and the
backward and forward substeps of the bonds `1, 2` move along `∓ (22/5) U`. -/
theorem isTTKSLStep_of_proj {g : Tensor (fun _ : Fin 3 => Fin 2)}
    (h₁ : ttRightProj oldCores 1 g = drift)
    (h₂ : ttLeftProj newCores 1 (ttRightProj oldCores 2 g) = (22 / 5 : ℝ) • tt newCores)
    (h₃ : ttLeftProj newCores 2 (ttRightProj oldCores 2 g) = (22 / 5 : ℝ) • tt newCores)
    (h₄ : ttLeftProj newCores 2 g = (22 / 5 : ℝ) • tt newCores) :
    IsTTKSLStep (fun _ _ => g) newCores oldCores 0 1 (tt oldCores) kPath sPath where
  leftOrth i _ := isLeftOrth_newCores i
  rightOrth i _ := isRightOrth_oldCores i
  start := ttRightProj_tt (by norm_num) fun i _ => isRightOrth_oldCores i
  kSol k hk := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    · exact Exactness.odeSolution_add_smul_of_const (c := drift) (fun _ _ => by
        simp only [ttKProj, mul_apply_eq_comp, ttLeftProj_zero, one_apply_eq_self, zero_add, h₁])
        (tt oldCores) 0 1
    · exact Exactness.odeSolution_add_smul_of_const (c := (22 / 5 : ℝ) • tt newCores)
        (fun _ _ => by simp only [ttKProj, mul_apply_eq_comp, Nat.reduceAdd, h₂])
        ((3 / 5 : ℝ) • tt newCores) 0 1
    · exact Exactness.odeSolution_add_smul_of_const (c := (22 / 5 : ℝ) • tt newCores)
        (fun _ _ => by
          simp only [ttKProj, mul_apply_eq_comp, Nat.reduceAdd, ttRightProj_self,
            one_apply_eq_self, h₄])
        ((3 / 5 : ℝ) • tt newCores) 0 1
  kStart₀ := by simp [kPath]
  kCap k hk := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · change ttLeftProj newCores (0 + 1) (tt oldCores + (1 : ℝ) • drift) =
        tt oldCores + (1 : ℝ) • drift
      rw [one_smul, tt_oldCores_add_drift, map_smul,
        ttLeftProj_tt (by norm_num) fun i _ => isLeftOrth_newCores i]
    · change ttLeftProj newCores (1 + 1)
          ((3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores)) =
        (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores)
      rw [map_add, map_smul, map_smul, map_smul,
        ttLeftProj_tt (by norm_num) fun i _ => isLeftOrth_newCores i]
  sSol k hk := by
    have hS : ttSProj newCores oldCores k g = (22 / 5 : ℝ) • tt newCores := by
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · simp only [ttSProj, mul_apply_eq_comp, zero_add, h₁, ttLeftProj_one_drift]
      · simp only [ttSProj, mul_apply_eq_comp, Nat.reduceAdd, h₃]
    exact Exactness.odeSolution_add_smul_of_const (c := -((22 / 5 : ℝ) • tt newCores))
      (fun _ _ => by rw [hS]) ((5 : ℝ) • tt newCores) 0 1
  sStart k hk := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · change (5 : ℝ) • tt newCores + (0 : ℝ) • -((22 / 5 : ℝ) • tt newCores) =
        tt oldCores + (1 : ℝ) • drift
      rw [zero_smul, add_zero, one_smul, tt_oldCores_add_drift]
    · change (5 : ℝ) • tt newCores + (0 : ℝ) • -((22 / 5 : ℝ) • tt newCores) =
        (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores)
      module
  kStart k hk := by
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals
      change (3 / 5 : ℝ) • tt newCores + (0 : ℝ) • ((22 / 5 : ℝ) • tt newCores) =
        (5 : ℝ) • tt newCores + (1 : ℝ) • -((22 / 5 : ℝ) • tt newCores)
      module

/-- The example step for the field `c` itself (`F(t, Y) = Ȧ(t)` for `A(t) = e₀ ⊗ e₀ ⊗ e₀ + t c`). -/
theorem isTTKSLStep_drift :
    IsTTKSLStep (fun _ _ => drift) newCores oldCores 0 1 (tt oldCores) kPath sPath :=
  isTTKSLStep_of_proj ttRightProj_one_drift
    (by rw [ttRightProj_two_drift, ttLeftProj_one_drift])
    (by rw [ttRightProj_two_drift, ttLeftProj_two_drift]) ttLeftProj_two_drift

/-- The example step for the field `c + n`: the same substeps, since `n` is in the kernel of
every substep projector. -/
theorem isTTKSLStep_drift_add_normalDrift :
    IsTTKSLStep (fun _ _ => drift + normalDrift) newCores oldCores 0 1 (tt oldCores) kPath
      sPath :=
  isTTKSLStep_of_proj
    (by rw [map_add, ttRightProj_one_drift, ttRightProj_one_normalDrift, add_zero])
    (by rw [map_add, ttRightProj_two_drift, ttRightProj_two_normalDrift, map_add,
      ttLeftProj_one_drift, ttLeftProj_one_normalDrift, add_zero])
    (by rw [map_add, ttRightProj_two_drift, ttRightProj_two_normalDrift, map_add,
      ttLeftProj_two_drift, ttLeftProj_two_normalDrift, add_zero])
    (by rw [map_add, ttLeftProj_two_drift, ttLeftProj_two_normalDrift, add_zero])

/-- The unfoldings of the target `A(1) = 5 U` factor through the interfaces of the new cores. -/
theorem unfold_target (k : ℕ) (hk : k ≤ 3) :
    unfold (fun i : Fin 3 => i.val < k) (tt oldCores + (1 : ℝ) • drift) =
      ttLeft newCores k * ((5 : ℝ) • (1 : Matrix Unit Unit ℝ)) * (ttRight newCores k)ᵀ := by
  rw [one_smul, tt_oldCores_add_drift, unfold_smul, unfold_tt newCores k hk, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]

/-- The right overlaps of the target with the old cores are invertible at the inner bonds. -/
theorem isUnit_overlap {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    IsUnit ((ttRight newCores k)ᵀ * ttRight oldCores k) := by
  rw [ttRight_newCores hk, ttRight_transpose_mul_self k hk3 fun i _ => isRightOrth_oldCores i]
  exact isUnit_one

/-- The target `A(1)` is recoverable from `P_{>k+1} A(1)` at every inner bond. -/
theorem isRecoverable_target :
    ∀ k, k + 1 < 3 → Exactness.IsRecoverable
      (Set.range (actOn (ι := fun _ : Fin 3 => Fin 2) fun i : Fin 3 => i.val < k + 1))
      (ttRightProj oldCores (k + 1)) (tt oldCores + (1 : ℝ) • drift) := fun k hk =>
  isRecoverable_ttRightProj_of_isUnit hk.le (fun i _ => isRightOrth_oldCores i)
    (unfold_target (k + 1) hk.le) (isUnit_overlap (Nat.succ_pos k) hk.le)

end TTKSLExample

section Examples

open TTKSLExample

/-- `IsTTKSLStep.eq_add_ttTangentProj` on the example: the step from `e₀ ⊗ e₀ ⊗ e₀` along
`A(t) = e₀ ⊗ e₀ ⊗ e₀ + t c` ends at the start value plus the TT tangent projection of
`A(1) - A(0)`, although its last forward substep moves along the new core `u`. -/
example : (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores) =
    tt oldCores + ttTangentProj newCores oldCores
      ((tt oldCores + (1 : ℝ) • drift) - (tt oldCores + (0 : ℝ) • drift)) :=
  isTTKSLStep_drift.eq_add_ttTangentProj zero_le_one (A := fun t => tt oldCores + t • drift)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by norm_num)

/-- `IsTTKSLStep.kStep_eq_ttRightProj` on the example, for core `1`: the forward substep ends
at `P_{>2} A(1)`. -/
example : (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores) =
    ttRightProj oldCores 2 (tt oldCores + (1 : ℝ) • drift) :=
  isTTKSLStep_drift.kStep_eq_ttRightProj zero_le_one (A := fun t => tt oldCores + t • drift)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by simp) isRecoverable_target 1 (by norm_num)

/-- `IsTTKSLStep.sStep_eq_ttLeftProj` on the example, for bond `1`: the backward substep ends at
`P_{≤1} A(0) = ⟨u, e₀⟩ U = (3/5) U`. -/
example : (5 : ℝ) • tt newCores + (1 : ℝ) • -((22 / 5 : ℝ) • tt newCores) =
    ttLeftProj newCores 1 (tt oldCores + (0 : ℝ) • drift) :=
  isTTKSLStep_drift.sStep_eq_ttLeftProj zero_le_one (A := fun t => tt oldCores + t • drift)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by simp) isRecoverable_target 0 (by norm_num)

/-- `IsTTKSLStep.exact` on the example: the last forward substep, `(3/5 + 22/5) U`, reproduces
`A(1) = e₀ ⊗ e₀ ⊗ e₀ + c`. -/
example : (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores) =
    tt oldCores + (1 : ℝ) • drift :=
  isTTKSLStep_drift.exact zero_le_one (A := fun t => tt oldCores + t • drift)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by simp) isRecoverable_target (by norm_num)

/-- `isRecoverable_ttRightProj_of_isUnit` at bond `2`: `A(1)⟨2⟩ = X_{≤2} (5 • 1) X_{>2}ᵀ` with the
interfaces of the new cores, and the overlap `X_{>2}ᵀ X_{>2}(old) = 1`. -/
example : Exactness.IsRecoverable
    (Set.range (actOn (ι := fun _ : Fin 3 => Fin 2) fun i : Fin 3 => i.val < 2))
    (ttRightProj oldCores 2) (tt oldCores + (1 : ℝ) • drift) :=
  isRecoverable_ttRightProj_of_isUnit (by norm_num) (fun i _ => isRightOrth_oldCores i)
    (unfold_target 2 (by norm_num)) (isUnit_overlap (by norm_num) (by norm_num))

/-- `IsTTKSLStep.exact_of_isUnit` on the example, with the factorizations
`A(1)⟨k⟩ = X_{≤k} (5 • 1) X_{>k}ᵀ` of `unfold_target`. -/
example : (3 / 5 : ℝ) • tt newCores + (1 : ℝ) • ((22 / 5 : ℝ) • tt newCores) =
    tt oldCores + (1 : ℝ) • drift :=
  isTTKSLStep_drift.exact_of_isUnit zero_le_one (A := fun t => tt oldCores + t • drift)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by simp) (by norm_num)
    (Uf := fun k => ttLeft newCores k) (S := fun _ => (5 : ℝ) • (1 : Matrix Unit Unit ℝ))
    (W := fun k => ttRight newCores k) (fun k _ hk => unfold_target k hk.le)
    (fun k hk0 hk => isUnit_overlap hk0 hk.le)

end Examples

end LeanDLRA.Tensor

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
* `TTKSLExample`: one-element modes and bonds, the constant field `c = tt (cores d) ≠ 0` and
  straight-line substeps form a step of the integrator for every number `d ≥ 1` of cores; the
  examples of this file and of `Tensor/TT/ProjectorSplittingError.lean` use it.

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

/-! ### Example: a constant field on one-element modes -/

namespace TTKSLExample

/-- The cores `C(α, x, α') = 1` of the all-ones tensor train on `d` one-element modes with
one-element bonds. -/
def cores (d : ℕ) : TTCores (fun _ : Fin d => Fin 1) (fun _ => Unit) := fun _ _ _ _ => 1

/-- The all-ones tensor `c = tt (cores d)`. -/
noncomputable def c (d : ℕ) : Tensor (fun _ : Fin d => Fin 1) := tt (cores d)

/-- The cores of `c` are left-orthogonal. -/
theorem isLeftOrth (d : ℕ) (i : Fin d) : IsLeftOrth (cores d) i := fun b b' => by
  cases b; cases b'
  simp [cores]

/-- The cores of `c` are right-orthogonal. -/
theorem isRightOrth (d : ℕ) (i : Fin d) : IsRightOrth (cores d) i := fun a a' => by
  cases a; cases a'
  simp [cores]

/-- Every entry of `c` is `1`. -/
theorem c_apply (d : ℕ) (x : Fin d → Fin 1) : c d x = 1 := by
  rw [c, tt_rankOne]
  simp [cores]

/-- The tensor `c` is not zero. -/
theorem c_ne_zero (d : ℕ) : c d ≠ 0 := by
  intro h
  have h1 := c_apply d fun _ => 0
  rw [h] at h1
  simp at h1

/-- `c` is fixed by every left interface projector of its cores. -/
theorem ttLeftProj_c {d k : ℕ} (hk : k ≤ d) : ttLeftProj (cores d) k (c d) = c d :=
  ttLeftProj_tt hk fun i _ => isLeftOrth d i

/-- `c` is fixed by every right interface projector of its cores. -/
theorem ttRightProj_c {d k : ℕ} (hk : k ≤ d) : ttRightProj (cores d) k (c d) = c d :=
  ttRightProj_tt hk fun i _ => isRightOrth d i

/-- **A TT projector-splitting step with a constant field.** For `d ≥ 1` one-element modes, the
constant field `c`, the start value `a c + t₀ c` and the straight-line substeps
`YK k t = a c + t c`, `YS k t = (a + t₁ + t₀) c - t c` form a step from `t₀` to `t₁`. -/
theorem isTTKSLStep {d : ℕ} (hd : 0 < d) (a t₀ t₁ : ℝ) :
    IsTTKSLStep (fun _ _ => c d) (cores d) (cores d) t₀ t₁ (a • c d + t₀ • c d)
      (fun _ t => a • c d + t • c d) (fun _ t => (a • c d + t₁ • c d + t₀ • c d) + t • -c d) where
  leftOrth i _ := isLeftOrth d i
  rightOrth i _ := isRightOrth d i
  start := by rw [map_add, map_smul, map_smul, ttRightProj_c hd]
  kSol k hk := Exactness.odeSolution_add_smul_of_const (fun _ _ => by
    simp only [ttKProj, mul_apply_eq_comp, ttRightProj_c (Nat.succ_le_of_lt hk),
      ttLeftProj_c hk.le]) _ _ _
  kStart₀ := rfl
  kCap k hk := by rw [map_add, map_smul, map_smul, ttLeftProj_c hk.le]
  sSol k hk := Exactness.odeSolution_add_smul_of_const (fun _ _ => by
    simp only [ttSProj, mul_apply_eq_comp, ttRightProj_c hk.le,
      ttLeftProj_c hk.le]) _ _ _
  sStart _ _ := by simp only [smul_neg]; abel
  kStart _ _ := by simp only [smul_neg]; abel

/-- Multiples of `c` are recoverable from their image under any right interface projector of
`cores d`, modulo any class of operators (with `T = 1`). -/
theorem isRecoverable {d k : ℕ} (hk : k ≤ d)
    (𝓛 : Set (Tensor (fun _ : Fin d => Fin 1) →L[ℝ] Tensor (fun _ : Fin d => Fin 1))) (a t : ℝ) :
    Exactness.IsRecoverable 𝓛 (ttRightProj (cores d) k) (a • c d + t • c d) :=
  ⟨1, fun _ _ _ => rfl, by
    rw [one_apply_eq_self, map_add, map_smul, map_smul, ttRightProj_c hk]⟩

end TTKSLExample

section Examples

open TTKSLExample

/-- Non-vacuity of `IsTTKSLStep.eq_add_ttTangentProj`: three cores, the constant field `c ≠ 0`,
`A t = c + t c`, one step from `0` to `1`. -/
example : (1 : ℝ) • c 3 + (1 : ℝ) • c 3 = ((1 : ℝ) • c 3 + (0 : ℝ) • c 3) +
    ttTangentProj (cores 3) (cores 3)
      (((1 : ℝ) • c 3 + (1 : ℝ) • c 3) - ((1 : ℝ) • c 3 + (0 : ℝ) • c 3)) :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).eq_add_ttTangentProj zero_le_one
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) (by norm_num)

/-- Non-vacuity of `IsTTKSLStep.kStep_eq_ttRightProj` (same data). -/
example : ∀ k < 3, (1 : ℝ) • c 3 + (1 : ℝ) • c 3 =
    ttRightProj (cores 3) (k + 1) ((1 : ℝ) • c 3 + (1 : ℝ) • c 3) :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).kStep_eq_ttRightProj zero_le_one
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) rfl fun _ hk => isRecoverable (by omega) _ 1 1

/-- Non-vacuity of `IsTTKSLStep.sStep_eq_ttLeftProj` (same data). -/
example : ∀ k, k + 1 < 3 → ((1 : ℝ) • c 3 + (1 : ℝ) • c 3 + (0 : ℝ) • c 3) + (1 : ℝ) • -c 3 =
    ttLeftProj (cores 3) (k + 1) ((1 : ℝ) • c 3 + (0 : ℝ) • c 3) :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).sStep_eq_ttLeftProj zero_le_one
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) rfl fun _ hk => isRecoverable (by omega) _ 1 1

/-- Non-vacuity of `IsTTKSLStep.exact` (same data). -/
example : (1 : ℝ) • c 3 + (1 : ℝ) • c 3 = (1 : ℝ) • c 3 + (1 : ℝ) • c 3 :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).exact zero_le_one
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) rfl (fun _ hk => isRecoverable (by omega) _ 1 1)
    (by norm_num)

/-- Non-vacuity of `isRecoverable_ttRightProj_of_isUnit`: the tensor train `c` itself, with the
factorization `c⟨2⟩ = X_{≤2} 1 X_{>2}ᵀ` and the overlap `X_{>2}ᵀ X_{>2} = 1`. -/
example : Exactness.IsRecoverable
    (Set.range (actOn (ι := fun _ : Fin 3 => Fin 1) fun i : Fin 3 => i.val < 2))
    (ttRightProj (cores 3) 2) (c 3) :=
  isRecoverable_ttRightProj_of_isUnit (by norm_num) (fun i _ => isRightOrth 3 i)
    (U := ttLeft (cores 3) 2) (S := 1) (W := ttRight (cores 3) 2)
    (by rw [Matrix.mul_one]; exact unfold_tt (cores 3) 2 (by norm_num))
    (by rw [ttRight_transpose_mul_self 2 (by norm_num) fun i _ => isRightOrth 3 i]
        exact isUnit_one)

/-- Non-vacuity of `IsTTKSLStep.exact_of_isUnit` (data of the examples above; the unfoldings of
`A 1 = 2 c` factor as `X_{≤k} (2 • 1) X_{>k}ᵀ`). -/
example : (1 : ℝ) • c 3 + (1 : ℝ) • c 3 = (1 : ℝ) • c 3 + (1 : ℝ) • c 3 :=
  (isTTKSLStep (d := 3) (by norm_num) 1 0 1).exact_of_isUnit zero_le_one
    (A := fun t : ℝ => (1 : ℝ) • c 3 + t • c 3)
    (Exactness.isDerivRHS_add_smul _ _ 0 1) rfl (by norm_num)
    (Uf := fun k => ttLeft (cores 3) k) (S := fun _ => (2 : ℝ) • 1)
    (W := fun k => ttRight (cores 3) k)
    (fun k _ hk => by
      simp only [unfold_add, unfold_smul, c, unfold_tt (cores 3) k hk.le, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one]
      module)
    (fun k _ hk => by
      rw [ttRight_transpose_mul_self k hk.le fun i _ => isRightOrth 3 i]
      exact isUnit_one)

end Examples

end LeanDLRA.Tensor

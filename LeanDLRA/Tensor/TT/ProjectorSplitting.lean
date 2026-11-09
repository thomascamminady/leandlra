import LeanDLRA.Tensor.TT.Operations
import LeanDLRA.Tensor.TT.TangentProjector
import LeanDLRA.Integrators.ProjectorSplitting
import LeanDLRA.Foundations.Galerkin

/-!
# The tensor-train projector-splitting integrator (TT-KSL, one-site TDVP)

The projector-splitting integrator for tensor trains (Lubich–Oseledets–Vandereycken, arXiv
1407.2042; the one-site TDVP algorithm of Haegeman et al. as described in arXiv 2603.13990, §4.3;
the PS-TDVP of arXiv 2609.12848) splits the TT tangent projector
`P_Y = ∑_{k=1}^{d} P_{≤k-1} P_{>k} - ∑_{k=1}^{d-1} P_{≤k} P_{>k}` into its `2d - 1` terms and
integrates them one after the other in a left-to-right sweep: a forward substep with the
projector `P_{≤k-1} P_{>k}` updates core `k`, a backward substep with `P_{≤k} P_{>k}` updates the
bond matrix after a QR decomposition of the new core. In the 0-based numbering of the library the
forward projector of core `k` is `ttKProj A B k = P_{≤k} P_{>k+1}` and the backward projector of
bond `k + 1` is `ttSProj A B k = P_{≤k+1} P_{>k+1}`, built from the new left-orthogonal cores `A`
(cores `< k`, resp. `≤ k`, already updated) and the old right-orthogonal cores `B`.

## Core and bond coefficients

A substep only changes one core or one bond matrix. The new core is the **core coefficient**
`C̃(α, x_k, α') = ∑ X_{≤k}(w, α) Z(w, x_k, v) X_{>k+1}(v, α')` of the right-hand side (arXiv
2512.14950, Eqs. (3.7), (3.15), (3.23); the core-centred contraction `Q̂_k` of arXiv 2603.13990,
Eqs. (4.22)–(4.23)), the new bond matrix is the **bond coefficient**
`S̃ = X_{≤k}ᵀ Z⟨k⟩ X_{>k}` (arXiv 2512.14950, Eqs. (3.11), (3.19); the bond-centred contraction
`Q̂_k^B` of arXiv 2603.13990, Eq. (4.26)). Inserted back into the tensor train they give the
substep projectors applied to the right-hand side (`tt_update_ttCoreCoeff`,
`ttBond_ttBondCoeff`); they extract the core of a mixed canonical tensor train and the bond matrix
of a bond-centred one, and they are invariant under the substep projectors (arXiv 2603.13990,
Eqs. (4.23), (4.25), (4.26), (4.27)).

## The integrator

* `IsTTKSLDiscreteStep`: one step of the fully discrete (discretize-then-project) TT
  projector-splitting scheme of Wang–Hu (arXiv 2512.14950, §3, steps 1–5): forward substeps
  `Y_{2k+1} = P_{≤k} P_{>k+1} G_k(Y_{2k})` and backward substeps
  `Y_{2k+2} = P_{≤k+1} P_{>k+1} H_k(Y_{2k+1})` with arbitrary one-step maps `G_k`, `H_k` (the
  paper's `G_Δt`, `H_Δt`, Eqs. (3.4)–(3.5)), and the QR step as the capture condition
  `P_{≤k+1} Y_{2k+1} = Y_{2k+1}` (derived from a QR factorization of the new core in
  `capture_of_qr`).
* `IsTTKSLStep`: one step of the time-continuous TT projector-splitting integrator (arXiv
  1407.2042, §4; TDVP, arXiv 2603.13990, Eqs. (4.29)–(4.30)), with forward K-substeps
  `Y' = P_{≤k} P_{>k+1} F(t, Y)` and backward substeps `Y' = -P_{≤k+1} P_{>k+1} F(t, Y)`.

## Main results

* `tt_update_ttCoreCoeff`, `ttBond_ttBondCoeff`: the core and bond updates are the substep
  projectors; `ttCoreCoeff_tt_update`, `ttBondCoeff_ttBond`: extraction;
  `ttCoreCoeff_ttKProj`, `ttBondCoeff_ttSProj`: invariance (arXiv 2603.13990, (4.25), (4.27)).
* `ttTangentProj_eq_sum_substeps`, `sum_ttKSLOp_eq`: the signed substep projectors sum to the TT
  tangent projector `ttTangentProj A B`.
* `IsTTKSLDiscreteStep.fix_fwd`, `fix_bwd`, `fwd_eq_tt`, `bwd_eq_ttBond`, `euler_fwd`,
  `euler_bwd`, and **`IsTTKSLDiscreteStep.euler_consistency`**: with forward-Euler substeps
  `G = id + h F`, `H = id - h F` (arXiv 2512.14950, Eqs. (4.8), (4.17), (4.24)) one sweep is a
  Lie–Trotter splitting of the projected Euler step: `‖Y_{2d-1} - (Y₀ + h P F(Y₀))‖ ≤
  L B h² (2d - 1)(d - 1)` with `P = ttTangentProj A B`, an orthogonal projector.
* `norm_sub_euler_sum_le`: the abstract estimate behind it (a composition of Euler steps with
  contractive operators `Opⱼ` is the Euler step of `∑ Opⱼ` up to `L B h² ∑ j`).
* `IsTTKSLStep.mem_range_kProj`, `IsTTKSLStep.norm_eq` (**norm conservation** of the TT
  projector-splitting integrator / one-site TDVP for `⟪F(t, x), x⟫ = 0`, arXiv 2603.13990, §4.3,
  after Eq. (4.33)), `IsTTKSLStep.energy_eq` (**energy conservation** for `F = J ∇ℰ` with `J`
  skew and commuting with the substep projectors), and `IsTTKSLStep.isKSLStep` (for two modes the
  TT projector-splitting step is the matrix KSL step, so the robust error bound
  `IsKSLStep.local_error` applies).

The second-order Strang variant (arXiv 2512.14950, §3.2) and the robust error bound of arXiv
1407.2042 for `d > 2` are not formalized. Everything is real: complex tensor trains (quantum
states) enter only through a realification, which is not done at the level of cores.
-/

open scoped Matrix RealInnerProductSpace
open Set

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} {β : ℕ → Type*} [∀ k, Fintype (β k)]

/-! ### Assembling multi-indices around one core -/

section Assemble

/-- The multi-index with first `k` modes `w`, mode `k` equal to `c` and remaining modes `v`. -/
def assemble (k : ℕ) (hk : k < d) (w : ∀ i : {i : Fin d // i.val < k}, ι i) (c : ι ⟨k, hk⟩)
    (v : ∀ i : {i : Fin d // ¬ i.val < k + 1}, ι i) : ∀ i, ι i :=
  merge (fun i : Fin d => i.val < k) w ((suffixSuccEquiv k hk).symm (c, v))

variable (k : ℕ) (hk : k < d) (w : ∀ i : {i : Fin d // i.val < k}, ι i) (c : ι ⟨k, hk⟩)
  (v : ∀ i : {i : Fin d // ¬ i.val < k + 1}, ι i)

@[simp] lemma restrict_assemble_lt :
    Subtype.restrict (fun i : Fin d => i.val < k) (assemble k hk w c v) = w :=
  restrict_merge _ _ _

@[simp] lemma assemble_self : assemble k hk w c v ⟨k, hk⟩ = c := by
  have h := congrFun (restrict_not_merge (fun i : Fin d => i.val < k) w
    ((suffixSuccEquiv k hk).symm (c, v))) ⟨⟨k, hk⟩, lt_irrefl k⟩
  exact h.trans (suffixSuccEquiv_symm_apply_self k hk (c, v))

@[simp] lemma restrict_assemble_gt :
    Subtype.restrict (fun i : Fin d => ¬ i.val < k + 1) (assemble k hk w c v) = v := by
  funext i
  have h := congrFun (restrict_not_merge (fun i : Fin d => i.val < k) w
    ((suffixSuccEquiv k hk).symm (c, v))) ⟨i.1, fun h => i.2 (Nat.lt_succ_of_lt h)⟩
  exact h.trans (congrFun (restrictLE_suffixSuccEquiv_symm k hk (c, v)) i)

/-- Overriding the first `k` modes by `w` and the modes `> k` by `v` assembles `w`, `x_k`, `v`. -/
lemma override_override_eq_assemble (x : ∀ i, ι i) :
    override (fun i : Fin d => ¬ i.val < k + 1) (override (fun i : Fin d => i.val < k) x w) v =
      assemble k hk w (x ⟨k, hk⟩) v := by
  funext i
  by_cases h1 : i.val < k
  · have h2 : ¬ ¬ i.val < k + 1 := fun h => h (by omega)
    rw [override_apply_of_not (fun i : Fin d => ¬ i.val < k + 1) h2,
      override_apply_of (fun i : Fin d => i.val < k) h1]
    exact (congrFun (restrict_assemble_lt k hk w (x ⟨k, hk⟩) v) ⟨i, h1⟩).symm
  · by_cases h3 : i.val < k + 1
    · obtain rfl : i = ⟨k, hk⟩ := Fin.ext (show i.val = k by omega)
      rw [override_apply_of_not (fun i : Fin d => ¬ i.val < k + 1) (not_not.2 h3),
        override_apply_of_not (fun i : Fin d => i.val < k) h1, assemble_self]
    · rw [override_apply_of (fun i : Fin d => ¬ i.val < k + 1) h3]
      exact (congrFun (restrict_assemble_gt k hk w (x ⟨k, hk⟩) v) ⟨i, h3⟩).symm

end Assemble

/-! ### Core and bond coefficients -/

section Coefficients

variable [∀ i, Fintype (ι i)]

/-- The **core coefficient** of a tensor `Z` at core `k` with respect to the left interface of `A`
and the right interface of `B`:
`C̃(α, c, α') = ∑_{w, v} X_{≤k}(w, α) Z(w, c, v) X_{>k+1}(v, α')` (arXiv 2512.14950, Eqs. (3.7),
(3.15), (3.23); the core-centred contraction of arXiv 2603.13990, Eqs. (4.22)–(4.23)). -/
noncomputable def ttCoreCoeff (A B : TTCores ι β) (k : ℕ) (hk : k < d) (Z : Tensor ι) :
    β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ :=
  fun a c b => ∑ w, ∑ v, ttLeft A k w a * Z (assemble k hk w c v) * ttRight B (k + 1) v b

/-- The **bond coefficient** `S̃ = X_{≤k}ᵀ Z⟨k⟩ X_{>k}` of a tensor `Z` at bond `k` (arXiv
2512.14950, Eqs. (3.11), (3.19); the bond-centred contraction of arXiv 2603.13990, Eq. (4.26)). -/
noncomputable def ttBondCoeff (A B : TTCores ι β) (k : ℕ) (Z : Tensor ι) :
    Matrix (β k) (β k) ℝ :=
  fun a a' => ∑ w, ∑ v, ttLeft A k w a * Z (merge (fun i : Fin d => i.val < k) w v) *
    ttRight B k v a'

/-- **The core update is the forward substep projector** (arXiv 2512.14950, Steps 1b–1c, 3b–3c,
5b–5c; arXiv 2603.13990, Eq. (4.24)): inserting the core coefficient of `Z` as core `k` between
the left cores of `A` and the right cores of `B` gives `P_{≤k} P_{>k+1} Z`. -/
theorem tt_update_ttCoreCoeff (A B : TTCores ι β) (k : ℕ) (hk : k < d) (Z : Tensor ι) :
    tt (Function.update (ttMix A B k) ⟨k, hk⟩ (ttCoreCoeff A B k hk Z)) =
      ttLeftProj A k (ttRightProj B (k + 1) Z) := by
  ext x
  rw [tt_update_apply, ttLeft_ttMix A B le_rfl, ttRight_ttMix A B (Nat.le_succ k), ttLeftProj,
    actOn_mul_transpose_apply]
  simp only [ttRightProj, actOn_mul_transpose_apply,
    restrict_override_of_disjoint (p := fun i : Fin d => i.val < k)
      (q := fun i : Fin d => ¬ i.val < k + 1) (fun i hi hn => hn (by omega)),
    override_override_eq_assemble k hk, ttCoreCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun v _ => by ring)

/-- **The bond update is the backward substep projector** (arXiv 2512.14950, Steps 2b–2c,
4b–4c; arXiv 2603.13990, Eq. (4.27)): the bond-centred tensor train with the bond coefficient of
`Z` is `P_{≤k} P_{>k} Z`. -/
theorem ttBond_ttBondCoeff (A B : TTCores ι β) (k : ℕ) (Z : Tensor ι) :
    ttBond A B k (ttBondCoeff A B k Z) = ttLeftProj A k (ttRightProj B k Z) := by
  have hm : ∀ (x : ∀ i, ι i) w v, override (fun i : Fin d => ¬ i.val < k)
      (override (fun i : Fin d => i.val < k) x w) v = merge (fun i : Fin d => i.val < k) w v :=
    fun x w v => by
      funext i
      by_cases hi : i.val < k
      · rw [override_apply_of_not (fun i : Fin d => ¬ i.val < k) (not_not.2 hi),
          override_apply_of (fun i : Fin d => i.val < k) hi]
        simp [merge, hi]
      · rw [override_apply_of (fun i : Fin d => ¬ i.val < k) hi]
        simp [merge, hi]
  ext x
  rw [ttBond_apply, ttLeftProj, actOn_mul_transpose_apply]
  simp only [ttRightProj, actOn_mul_transpose_apply,
    restrict_override_of_disjoint (p := fun i : Fin d => i.val < k)
      (q := fun i : Fin d => ¬ i.val < k) (fun i hi hn => hn hi), hm, ttBondCoeff,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun v _ => by ring)

/-- Four nested finite sums can be reordered. -/
private lemma sum_comm4 {α₁ α₂ α₃ α₄ : Type*} [Fintype α₁] [Fintype α₂] [Fintype α₃]
    [Fintype α₄] (f : α₁ → α₂ → α₃ → α₄ → ℝ) :
    ∑ w, ∑ v, ∑ a, ∑ b, f w v a b = ∑ a, ∑ b, ∑ w, ∑ v, f w v a b :=
  calc ∑ w, ∑ v, ∑ a, ∑ b, f w v a b = ∑ w, ∑ a, ∑ v, ∑ b, f w v a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ w, ∑ v, ∑ b, f w v a b := Finset.sum_comm
    _ = ∑ a, ∑ w, ∑ b, ∑ v, f w v a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ w, ∑ v, f w v a b := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Contracting `L M Rᵀ` with orthonormal `L`, `R` from both sides recovers `M`. -/
private lemma sum_sum_orthonormal {W V R₁ R₂ : Type*} [Fintype W] [Fintype V] [Fintype R₁]
    [Fintype R₂] [DecidableEq R₁] [DecidableEq R₂] {L : Matrix W R₁ ℝ} {R : Matrix V R₂ ℝ}
    (hL : Lᵀ * L = 1) (hR : Rᵀ * R = 1) (M : R₁ → R₂ → ℝ) (a : R₁) (b : R₂) :
    ∑ w, ∑ v, L w a * (∑ a', ∑ b', L w a' * M a' b' * R v b') * R v b = M a b := by
  have hL' : ∀ a a', ∑ w, L w a * L w a' = if a = a' then 1 else 0 := fun a a' => by
    have := congrFun (congrFun hL a) a'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hR' : ∀ b' b, ∑ v, R v b' * R v b = if b' = b then 1 else 0 := fun b' b => by
    have := congrFun (congrFun hR b') b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc ∑ w, ∑ v, L w a * (∑ a', ∑ b', L w a' * M a' b' * R v b') * R v b
      = ∑ w, ∑ v, ∑ a', ∑ b', (L w a * L w a') * M a' b' * (R v b' * R v b) :=
        Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b' _ => by ring
    _ = ∑ a', ∑ b', ∑ w, ∑ v, (L w a * L w a') * M a' b' * (R v b' * R v b) := sum_comm4 _
    _ = ∑ a', ∑ b', (∑ w, L w a * L w a') * M a' b' * (∑ v, R v b' * R v b) :=
        Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
    _ = M a b := by simp [hL', hR']

variable [∀ k, DecidableEq (β k)]

/-- **Extraction of the core** (arXiv 2603.13990, Eq. (4.23)): the core coefficient of a mixed
canonical tensor train (left-orthogonal cores `A` before `k`, right-orthogonal cores `B` after
`k`) with core `M` at `k` is `M`. -/
theorem ttCoreCoeff_tt_update [Subsingleton (β 0)] [Subsingleton (β d)] {A B : TTCores ι β}
    {k : ℕ} (hk : k < d) (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i)
    (M : β k → ι ⟨k, hk⟩ → β (k + 1) → ℝ) :
    ttCoreCoeff A B k hk (tt (Function.update (ttMix A B k) ⟨k, hk⟩ M)) = M := by
  funext a c b
  simp only [ttCoreCoeff, tt_update_apply, ttLeft_ttMix A B le_rfl,
    ttRight_ttMix A B (Nat.le_succ k), restrict_assemble_lt, assemble_self,
    restrict_assemble_gt]
  exact sum_sum_orthonormal (ttLeft_transpose_mul_self k hk.le hA)
    (ttRight_transpose_mul_self (k + 1) hk hB) (fun a' b' => M a' c b') a b

/-- **Extraction of the bond matrix** (arXiv 2603.13990, Eq. (4.26)): the bond coefficient of a
bond-centred tensor train with orthonormal interfaces is its bond matrix. -/
theorem ttBondCoeff_ttBond [Subsingleton (β 0)] [Subsingleton (β d)] {A B : TTCores ι β}
    {k : ℕ} (hk : k ≤ d) (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k ≤ i.val → IsRightOrth B i) (S : Matrix (β k) (β k) ℝ) :
    ttBondCoeff A B k (ttBond A B k S) = S := by
  funext a a'
  simp only [ttBondCoeff, ttBond_apply, restrict_merge, restrict_not_merge]
  exact sum_sum_orthonormal (ttLeft_transpose_mul_self k hk hA)
    (ttRight_transpose_mul_self k hk hB) S a a'

end Coefficients

/-! ### The substep projectors -/

section Substeps

/-- The **forward substep projector** of core `k`: `P_{≤k} P_{>k+1}` (the paper's
`P_{≤k-1} P_{>k}` for its core `k + 1`; arXiv 2603.13990, Eq. (4.29), first line). -/
noncomputable def ttKProj [∀ i, Fintype (ι i)] (A B : TTCores ι β) (k : ℕ) :
    Tensor ι →L[ℝ] Tensor ι :=
  ttLeftProj A k * ttRightProj B (k + 1)

/-- The **backward substep projector** of bond `k + 1`: `P_{≤k+1} P_{>k+1}` (arXiv 2603.13990,
Eq. (4.29), second line). -/
noncomputable def ttSProj [∀ i, Fintype (ι i)] (A B : TTCores ι β) (k : ℕ) :
    Tensor ι →L[ℝ] Tensor ι :=
  ttLeftProj A (k + 1) * ttRightProj B (k + 1)

variable [∀ i, Fintype (ι i)]

/-- The TT tangent projector is the signed sum of the substep projectors (arXiv 2603.13990,
Eq. (4.28)). -/
theorem ttTangentProj_eq_sum_substeps (A B : TTCores ι β) :
    ttTangentProj A B =
      ∑ k ∈ Finset.range d, ttKProj A B k - ∑ k ∈ Finset.range (d - 1), ttSProj A B k := rfl

/-- The `j`-th signed substep operator of one sweep: `ttKProj A B (j / 2)` for even `j` and
`-ttSProj A B (j / 2)` for odd `j`. -/
noncomputable def ttKSLOp (A B : TTCores ι β) (j : ℕ) : Tensor ι →L[ℝ] Tensor ι :=
  if j % 2 = 0 then ttKProj A B (j / 2) else -ttSProj A B (j / 2)

lemma ttKSLOp_even (A B : TTCores ι β) (k : ℕ) : ttKSLOp A B (2 * k) = ttKProj A B k := by
  simp [ttKSLOp]

lemma ttKSLOp_odd (A B : TTCores ι β) (k : ℕ) : ttKSLOp A B (2 * k + 1) = -ttSProj A B k := by
  simp only [ttKSLOp, Nat.mul_add_mod, Nat.one_mod, one_ne_zero, ↓reduceIte]
  congr 2
  omega

/-- The signed substep operators of one sweep over `n + 1` cores add up to the alternating sum
of the substep projectors. -/
theorem sum_ttKSLOp_eq (A B : TTCores ι β) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1), ttKSLOp A B j =
      ∑ k ∈ Finset.range (n + 1), ttKProj A B k - ∑ k ∈ Finset.range n, ttSProj A B k := by
  induction n with
  | zero => simp [ttKSLOp_even A B 0]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, ttKSLOp_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by ring,
      ttKSLOp_even]
    simp only [Finset.sum_range_succ]
    abel

/-- One sweep of `2d - 1` substeps: the signed substep operators add up to the TT tangent
projector `ttTangentProj A B`. -/
theorem sum_ttKSLOp_eq_ttTangentProj (A B : TTCores ι β) (hd : 0 < d) :
    ∑ j ∈ Finset.range (2 * d - 1), ttKSLOp A B j = ttTangentProj A B := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, sum_ttKSLOp_eq, ttTangentProj_eq_sum_substeps,
    Nat.add_sub_cancel]

variable [∀ k, DecidableEq (β k)] [Subsingleton (β 0)] [Subsingleton (β d)]

/-- The forward substep projector is an orthogonal projector (cores `< k` of `A`
left-orthogonal, cores `> k` of `B` right-orthogonal). -/
theorem isOrthProj_ttKProj {A B : TTCores ι β} {k : ℕ} (hk : k < d)
    (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) : IsOrthProj (ttKProj A B k) :=
  isOrthProj_ttLeftProj_mul_ttRightProj (Nat.le_succ k) hk hA hB

/-- The backward substep projector is an orthogonal projector. -/
theorem isOrthProj_ttSProj {A B : TTCores ι β} {k : ℕ} (hk : k + 1 ≤ d)
    (hA : ∀ i : Fin d, i.val < k + 1 → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) : IsOrthProj (ttSProj A B k) :=
  isOrthProj_ttLeftProj_mul_ttRightProj le_rfl hk hA hB

/-- **Invariance of the core coefficient** (arXiv 2603.13990, Eq. (4.25)): the core coefficient
does not see the part of `Z` outside the range of the forward substep projector. -/
theorem ttCoreCoeff_ttKProj {A B : TTCores ι β} {k : ℕ} (hk : k < d)
    (hA : ∀ i : Fin d, i.val < k → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) (Z : Tensor ι) :
    ttCoreCoeff A B k hk (ttKProj A B k Z) = ttCoreCoeff A B k hk Z := by
  change ttCoreCoeff A B k hk (ttLeftProj A k (ttRightProj B (k + 1) Z)) = _
  rw [← tt_update_ttCoreCoeff, ttCoreCoeff_tt_update hk hA hB]

/-- **Invariance of the bond coefficient** (arXiv 2603.13990, Eq. (4.27)). -/
theorem ttBondCoeff_ttSProj {A B : TTCores ι β} {k : ℕ} (hk : k + 1 ≤ d)
    (hA : ∀ i : Fin d, i.val < k + 1 → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) (Z : Tensor ι) :
    ttBondCoeff A B (k + 1) (ttSProj A B k Z) = ttBondCoeff A B (k + 1) Z := by
  change ttBondCoeff A B (k + 1) (ttLeftProj A (k + 1) (ttRightProj B (k + 1) Z)) = _
  rw [← ttBond_ttBondCoeff, ttBondCoeff_ttBond hk hA hB]

omit [Subsingleton (β 0)] in
/-- If the forward projector of core `k` fixes `W`, so does the right projector `P_{>k+1}`. -/
theorem ttRightProj_fix_of_ttKProj {A B : TTCores ι β} {k : ℕ} (hk : k < d)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) {W : Tensor ι}
    (hW : ttKProj A B k W = W) : ttRightProj B (k + 1) W = W := by
  have hc : ttLeftProj A k (ttRightProj B (k + 1) (ttRightProj B (k + 1) W)) =
      ttRightProj B (k + 1) (ttLeftProj A k (ttRightProj B (k + 1) W)) :=
    congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T (ttRightProj B (k + 1) W))
      (ttLeftProj_comm_ttRightProj A B (j := k) (k := k + 1) (Nat.le_succ _))
  have hRR := (isOrthProj_ttRightProj (B := B) hk hB).idem W
  calc ttRightProj B (k + 1) W = ttRightProj B (k + 1) (ttKProj A B k W) := by rw [hW]
    _ = ttKProj A B k W := by
      change ttRightProj B (k + 1) (ttLeftProj A k (ttRightProj B (k + 1) W)) =
        ttLeftProj A k (ttRightProj B (k + 1) W)
      rw [← hc, hRR]
    _ = W := hW

omit [Subsingleton (β 0)] in
/-- After the QR step: a tensor in the range of the forward projector of core `k` that is
captured by the new left interface `X_{≤k+1}` lies in the range of the backward projector. -/
theorem ttSProj_fix_of_ttKProj {A B : TTCores ι β} {k : ℕ} (hk : k < d)
    (hB : ∀ i : Fin d, k + 1 ≤ i.val → IsRightOrth B i) {W : Tensor ι}
    (hW : ttKProj A B k W = W) (hcap : ttLeftProj A (k + 1) W = W) :
    ttSProj A B k W = W := by
  change ttLeftProj A (k + 1) (ttRightProj B (k + 1) W) = W
  rw [ttRightProj_fix_of_ttKProj hk hB hW, hcap]

/-- The range of the backward projector of bond `k + 1` lies in the range of the forward
projector of core `k + 1` (nested right interfaces). -/
theorem ttKProj_succ_fix_of_ttSProj {A B : TTCores ι β} {k : ℕ} (hk : k + 1 < d)
    (hA : ∀ i : Fin d, i.val < k + 1 → IsLeftOrth A i)
    (hB : ∀ i : Fin d, k + 1 + 1 ≤ i.val → IsRightOrth B i) {W : Tensor ι}
    (hW : ttSProj A B k W = W) : ttKProj A B (k + 1) W = W := by
  have hRR : ttRightProj B (k + 1 + 1) (ttRightProj B (k + 1) W) = ttRightProj B (k + 1) W :=
    congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T W) (ttRightProj_succ_mul hk hB)
  have hLL := (isOrthProj_ttLeftProj hk.le hA).idem (ttRightProj B (k + 1) W)
  have hc : ttLeftProj A (k + 1) (ttRightProj B (k + 1 + 1) (ttRightProj B (k + 1) W)) =
      ttRightProj B (k + 1 + 1) (ttLeftProj A (k + 1) (ttRightProj B (k + 1) W)) :=
    congrArg (fun T : Tensor ι →L[ℝ] Tensor ι => T (ttRightProj B (k + 1) W))
      (ttLeftProj_comm_ttRightProj A B (j := k + 1) (k := k + 1 + 1) (Nat.le_succ _))
  rw [← hW]
  change ttLeftProj A (k + 1) (ttRightProj B (k + 1 + 1)
    (ttLeftProj A (k + 1) (ttRightProj B (k + 1) W))) =
    ttLeftProj A (k + 1) (ttRightProj B (k + 1) W)
  rw [← hc, hRR, hLL]

end Substeps

/-! ### Euler substeps: an abstract estimate -/

section EulerSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A composition of Euler steps is the Euler step of the summed operator up to `O(h²)`.** If
`Y_{j+1} = Y_j + h Op_j F(Y_j)` for `j < N` with contractive operators `Op_j`, an `L`-Lipschitz
`F` with `‖F(Y_j)‖ ≤ B` along the steps and `h ≥ 0`, then
`‖Y_N - (Y_0 + h (∑_{j<N} Op_j) F(Y_0))‖ ≤ L B h² ∑_{j<N} j`. This is the first-order consistency
of a Lie–Trotter splitting with Euler substeps. -/
theorem norm_sub_euler_sum_le {N : ℕ} {Op : ℕ → E →L[ℝ] E} (hOp : ∀ j < N, ∀ x, ‖Op j x‖ ≤ ‖x‖)
    {F : E → E} {L B h : ℝ} (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) {Y : ℕ → E}
    (hB : ∀ j < N, ‖F (Y j)‖ ≤ B) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hY : ∀ j < N, Y (j + 1) = Y j + h • Op j (F (Y j))) :
    ‖Y N - (Y 0 + h • (∑ j ∈ Finset.range N, Op j) (F (Y 0)))‖ ≤
      L * B * h ^ 2 * ∑ j ∈ Finset.range N, (j : ℝ) := by
  have hdrift : ∀ n ≤ N, ‖Y n - Y 0‖ ≤ n * (h * B) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < N := hn
      rw [hY n hn', show Y n + h • Op n (F (Y n)) - Y 0 = (Y n - Y 0) + h • Op n (F (Y n)) by
        abel]
      calc ‖(Y n - Y 0) + h • Op n (F (Y n))‖ ≤ ‖Y n - Y 0‖ + ‖h • Op n (F (Y n))‖ :=
            norm_add_le _ _
        _ ≤ n * (h * B) + h * B := by
          gcongr
          · exact ih hn'.le
          · rw [norm_smul, Real.norm_of_nonneg hh]
            exact mul_le_mul_of_nonneg_left ((hOp n hn' _).trans (hB n hn')) hh
        _ = ((n + 1 : ℕ) : ℝ) * (h * B) := by push_cast; ring
  have key : ∀ n ≤ N, ‖Y n - (Y 0 + h • (∑ j ∈ Finset.range n, Op j) (F (Y 0)))‖ ≤
      L * B * h ^ 2 * ∑ j ∈ Finset.range n, (j : ℝ) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hn' : n < N := hn
      have e : Y (n + 1) - (Y 0 + h • (∑ j ∈ Finset.range (n + 1), Op j) (F (Y 0))) =
          (Y n - (Y 0 + h • (∑ j ∈ Finset.range n, Op j) (F (Y 0)))) +
            h • Op n (F (Y n) - F (Y 0)) := by
        rw [hY n hn', Finset.sum_range_succ, _root_.add_apply, map_sub, smul_add,
          smul_sub]
        abel
      rw [e, Finset.sum_range_succ, mul_add]
      calc _ ≤ ‖Y n - (Y 0 + h • (∑ j ∈ Finset.range n, Op j) (F (Y 0)))‖ +
            ‖h • Op n (F (Y n) - F (Y 0))‖ := norm_add_le _ _
        _ ≤ L * B * h ^ 2 * ∑ j ∈ Finset.range n, (j : ℝ) + L * B * h ^ 2 * n := by
          gcongr
          · exact ih hn'.le
          · rw [norm_smul, Real.norm_of_nonneg hh]
            calc h * ‖Op n (F (Y n) - F (Y 0))‖ ≤ h * (L * ‖Y n - Y 0‖) :=
                  mul_le_mul_of_nonneg_left ((hOp n hn' _).trans (hF _ _)) hh
              _ ≤ h * (L * (n * (h * B))) := by
                  gcongr
                  exact hdrift n hn'.le
              _ = L * B * h ^ 2 * n := by ring
  exact key N le_rfl

end EulerSum

/-! ### The fully discrete TT projector-splitting scheme -/

section Discrete

variable [∀ i, Fintype (ι i)] [∀ k, DecidableEq (β k)]

/-- **One step of the fully discrete TT projector-splitting scheme** (Wang–Hu, arXiv 2512.14950,
§3, Steps 1–5, discretize-then-project). Starting from `Y 0` in form (I) (`P_{>1} Y₀ = Y₀`, i.e.
right-orthogonal cores `B i` for `i ≥ 1`), the forward substeps project the result of a one-step
map `G k` (the paper's `G_Δt`, Eq. (3.4)) onto `P_{≤k} P_{>k+1}`, the QR step makes the new left
core `A k` span the new tensor (`cap`, derived from a QR factorization in `capture_of_qr`), and
the backward substeps project the result of `H k` (the paper's `H_Δt`, Eq. (3.5)) onto
`P_{≤k+1} P_{>k+1}`. The result of the step is `Y (2 d - 1)`. -/
structure IsTTKSLDiscreteStep (G H : ℕ → Tensor ι → Tensor ι) (A B : TTCores ι β)
    (Y : ℕ → Tensor ι) : Prop where
  /-- The new left cores (from the QR steps) are left-orthogonal. -/
  leftOrth : ∀ i : Fin d, i.val + 1 < d → IsLeftOrth A i
  /-- The old right cores are right-orthogonal. -/
  rightOrth : ∀ i : Fin d, 0 < i.val → IsRightOrth B i
  /-- The starting tensor is in form (I). -/
  start : ttRightProj B 1 (Y 0) = Y 0
  /-- Forward substep of core `k` (Steps 1, 3, 5). -/
  fwd : ∀ k < d, Y (2 * k + 1) = ttKProj A B k (G k (Y (2 * k)))
  /-- QR step: the new left core `A k` captures the new tensor (Steps 1d, 3d). -/
  cap : ∀ k, k + 1 < d → ttLeftProj A (k + 1) (Y (2 * k + 1)) = Y (2 * k + 1)
  /-- Backward substep of bond `k + 1` (Steps 2, 4). -/
  bwd : ∀ k, k + 1 < d → Y (2 * k + 2) = ttSProj A B k (H k (Y (2 * k + 1)))

namespace IsTTKSLDiscreteStep

variable {G H : ℕ → Tensor ι → Tensor ι} {A B : TTCores ι β} {Y : ℕ → Tensor ι}

/-- The new core of a forward substep is the core coefficient of `G k (Y (2 k))`, so the
substep result is a tensor train with the cores of `A` before `k` and those of `B` after `k`
(arXiv 2512.14950, Steps 1b–1c, 3b–3c, 5b–5c). -/
theorem fwd_eq_tt (hs : IsTTKSLDiscreteStep G H A B Y) {k : ℕ} (hk : k < d) :
    Y (2 * k + 1) = tt (Function.update (ttMix A B k) ⟨k, hk⟩
      (ttCoreCoeff A B k hk (G k (Y (2 * k))))) := by
  rw [hs.fwd k hk, tt_update_ttCoreCoeff]
  rfl

/-- The new bond matrix of a backward substep is the bond coefficient of `H k (Y (2 k + 1))`
(arXiv 2512.14950, Steps 2b–2c, 4b–4c). -/
theorem bwd_eq_ttBond (hs : IsTTKSLDiscreteStep G H A B Y) {k : ℕ} (hk : k + 1 < d) :
    Y (2 * k + 2) = ttBond A B (k + 1) (ttBondCoeff A B (k + 1) (H k (Y (2 * k + 1)))) := by
  rw [hs.bwd k hk, ttBond_ttBondCoeff]
  rfl

variable [Subsingleton (β 0)] [Subsingleton (β d)]

/-- The tensors entering a forward substep lie in the range of its projector. -/
theorem fix_fwd [Unique (β 0)] (hs : IsTTKSLDiscreteStep G H A B Y) :
    ∀ k < d, ttKProj A B k (Y (2 * k)) = Y (2 * k)
  | 0, _ => by
    change ttLeftProj A 0 (ttRightProj B 1 (Y 0)) = Y 0
    rw [ttLeftProj_zero, hs.start]
    rfl
  | k + 1, hk => by
    have hk' : k + 1 < d := hk
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, hs.bwd k hk']
    exact ttKProj_succ_fix_of_ttSProj hk' (fun i hi => hs.leftOrth i (by omega))
      (fun i hi => hs.rightOrth i (by omega))
      ((isOrthProj_ttSProj hk'.le (fun i hi => hs.leftOrth i (by omega))
        fun i hi => hs.rightOrth i (by omega)).idem _)

/-- The tensors entering a backward substep lie in the range of its projector. -/
theorem fix_bwd (hs : IsTTKSLDiscreteStep G H A B Y) {k : ℕ} (hk : k + 1 < d) :
    ttSProj A B k (Y (2 * k + 1)) = Y (2 * k + 1) := by
  refine ttSProj_fix_of_ttKProj (by omega) (fun i hi => hs.rightOrth i (by omega)) ?_ (hs.cap k hk)
  rw [hs.fwd k (by omega)]
  exact (isOrthProj_ttKProj (by omega) (fun i hi => hs.leftOrth i (by omega))
    fun i hi => hs.rightOrth i (by omega)).idem _

/-- **Forward-Euler forward substeps** (arXiv 2512.14950, Eqs. (4.8), (4.17), (4.24)): with
`G k Y = Y + h F(Y)` the forward substep is the Euler step of the projected equation,
`Y_{2k+1} = Y_{2k} + h P_{≤k} P_{>k+1} F(Y_{2k})`. -/
theorem euler_fwd [Unique (β 0)] (hs : IsTTKSLDiscreteStep G H A B Y) {F : Tensor ι → Tensor ι}
    {h : ℝ} (hG : ∀ k Z, G k Z = Z + h • F Z) {k : ℕ} (hk : k < d) :
    Y (2 * k + 1) = Y (2 * k) + h • ttKProj A B k (F (Y (2 * k))) := by
  rw [hs.fwd k hk, hG, map_add, map_smul, hs.fix_fwd k hk]

/-- **Forward-Euler backward substeps** (arXiv 2512.14950, Eqs. (4.8), (4.17), (4.24)): with
`H k Y = Y - h F(Y)`, `Y_{2k+2} = Y_{2k+1} - h P_{≤k+1} P_{>k+1} F(Y_{2k+1})`. -/
theorem euler_bwd (hs : IsTTKSLDiscreteStep G H A B Y) {F : Tensor ι → Tensor ι} {h : ℝ}
    (hH : ∀ k Z, H k Z = Z - h • F Z) {k : ℕ} (hk : k + 1 < d) :
    Y (2 * k + 2) = Y (2 * k + 1) - h • ttSProj A B k (F (Y (2 * k + 1))) := by
  rw [hs.bwd k hk, hH, map_sub, map_smul, hs.fix_bwd hk]

/-- **The fully discrete scheme with Euler substeps is a Lie–Trotter splitting of the projected
Euler step** (arXiv 2512.14950, §3.2: "first-order accurate in time because it is based on a
Lie–Trotter splitting of the projection operator"). With `G = id + h F`, `H = id - h F`
(Eqs. (4.8), (4.17), (4.24)), `F` `L`-Lipschitz with `‖F(Y_j)‖ ≤ B` along the sweep, and `h ≥ 0`,
one sweep over
`d ≥ 1` cores satisfies
`‖Y_{2d-1} - (Y₀ + h P F(Y₀))‖ ≤ L B h² (2d - 1)(d - 1)` for the TT tangent projector
`P = ttTangentProj A B` at the new left cores `A` and the old right cores `B`.

This is the algebraic part of the first-order claim only: comparing `P F(Y₀)` with the tangent
projection at `Y₀` and with the exact solution (the robust error analysis of arXiv 1407.2042) is
not formalized. -/
theorem euler_consistency [Unique (β 0)] (hs : IsTTKSLDiscreteStep G H A B Y)
    {F : Tensor ι → Tensor ι} {L Bd h : ℝ} (hG : ∀ k Z, G k Z = Z + h • F Z)
    (hH : ∀ k Z, H k Z = Z - h • F Z) (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (hB : ∀ j < 2 * d - 1, ‖F (Y j)‖ ≤ Bd) (hL : 0 ≤ L) (hh : 0 ≤ h) (hd : 0 < d) :
    ‖Y (2 * d - 1) - (Y 0 + h • ttTangentProj A B (F (Y 0)))‖ ≤
      L * Bd * h ^ 2 * ((2 * d - 1) * (d - 1) : ℕ) := by
  have hOp : ∀ j < 2 * d - 1, ∀ x, ‖ttKSLOp A B j x‖ ≤ ‖x‖ := by
    intro j hj x
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [ttKSLOp_even]
      exact (isOrthProj_ttKProj (by omega) (fun i hi => hs.leftOrth i (by omega))
        fun i hi => hs.rightOrth i (by omega)).norm_le x
    · rw [ttKSLOp_odd, _root_.neg_apply, norm_neg]
      exact (isOrthProj_ttSProj (by omega) (fun i hi => hs.leftOrth i (by omega))
        fun i hi => hs.rightOrth i (by omega)).norm_le x
  have hY : ∀ j < 2 * d - 1, Y (j + 1) = Y j + h • ttKSLOp A B j (F (Y j)) := by
    intro j hj
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [ttKSLOp_even, hs.euler_fwd hG (by omega)]
    · rw [ttKSLOp_odd, _root_.neg_apply, smul_neg, ← sub_eq_add_neg,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring, hs.euler_bwd hH (by omega)]
  have h1 := norm_sub_euler_sum_le hOp hF hB hL hh hY
  rw [sum_ttKSLOp_eq_ttTangentProj A B hd] at h1
  refine h1.trans (le_of_eq ?_)
  congr 1
  have h2 := Finset.sum_range_id_mul_two (2 * d - 1)
  have h3 : (2 * d - 1) * (2 * d - 1 - 1) = 2 * ((2 * d - 1) * (d - 1)) := by
    rw [show 2 * d - 1 - 1 = 2 * (d - 1) by omega]
    ring
  rw [h3] at h2
  have h4 : ∑ i ∈ Finset.range (2 * d - 1), i = (2 * d - 1) * (d - 1) := by omega
  rw [← h4]
  push_cast
  rfl

end IsTTKSLDiscreteStep

/-- **The QR step gives the capture condition** (arXiv 2512.14950, Steps 1d, 3d): if the new
core `C̃ = ttCoreCoeff A B k hk (G k (Y (2 k)))` of a forward substep factors as
`C̃(α, x, γ) = ∑_β A_k(α, x, β) R(β, γ)` (a QR decomposition with left-orthogonal factor `A_k`),
then the new left interface `X_{≤k+1}` of `A` captures the substep result:
`P_{≤k+1} Y_{2k+1} = Y_{2k+1}`. -/
theorem capture_of_qr [Subsingleton (β 0)] {A B : TTCores ι β} {k : ℕ} (hk : k + 1 < d)
    (hA : ∀ i : Fin d, i.val < k + 1 → IsLeftOrth A i) {Z : Tensor ι}
    (R : Matrix (β (k + 1)) (β (k + 1)) ℝ)
    (hqr : ∀ a x c, ttCoreCoeff A B k (Nat.lt_of_succ_lt hk) Z a x c =
      ∑ b, A ⟨k, Nat.lt_of_succ_lt hk⟩ a x b * R b c) :
    ttLeftProj A (k + 1) (ttKProj A B k Z) = ttKProj A B k Z := by
  set hk' : k < d := Nat.lt_of_succ_lt hk
  set Gc := Function.update (ttMix A B k) ⟨k, hk'⟩ (ttCoreCoeff A B k hk' Z)
  set Gq := Function.update (ttMix A B (k + 1)) ⟨k + 1, hk⟩
    (fun b x b' => ∑ c, R b c * B ⟨k + 1, hk⟩ c x b')
  have hgauge : tt Gc = tt Gq := by
    refine tt_gauge (G := Gq) (G' := Gc) hk R (fun a x c => ?_) (fun b x b' => ?_)
      (fun i h1 h2 => ?_)
    · simp only [Gc, Gq, Function.update_self]
      rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), hqr]
      simp [ttMix]
    · simp only [Gc, Gq, Function.update_self]
      rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h)]
      simp [ttMix]
    · simp only [Gc, Gq]
      rw [Function.update_of_ne (fun h => h1 (congrArg Fin.val h)),
        Function.update_of_ne (fun h => h2 (congrArg Fin.val h))]
      simp only [ttMix]
      by_cases hi : i.val < k
      · simp [hi, show i.val < k + 1 by omega]
      · simp [hi, show ¬ i.val < k + 1 by omega]
  have hLq : ttLeftProj A (k + 1) = ttLeftProj Gq (k + 1) := by
    simp only [ttLeftProj]
    rw [ttLeft_congr (k + 1) fun i hi => ?_]
    simp only [Gq]
    rw [Function.update_of_ne (fun h => by have := congrArg Fin.val h; simp at this; omega)]
    simp [ttMix, hi]
  have hfix : ttLeftProj Gq (k + 1) (tt Gq) = tt Gq := by
    refine ttLeftProj_tt hk.le fun i hi => ?_
    have hne : i ≠ ⟨k + 1, hk⟩ := fun h => by have := congrArg Fin.val h; simp at this; omega
    intro b b'
    simp only [Gq, Function.update_of_ne hne, ttMix, hi, ↓reduceIte]
    exact hA i hi b b'
  change ttLeftProj A (k + 1) (ttLeftProj A k (ttRightProj B (k + 1) Z)) =
    ttLeftProj A k (ttRightProj B (k + 1) Z)
  rw [← tt_update_ttCoreCoeff A B k hk' Z]
  change ttLeftProj A (k + 1) (tt Gc) = tt Gc
  rw [hgauge, hLq, hfix]

end Discrete

/-! ### The time-continuous TT projector-splitting integrator -/

section Continuous

variable [∀ i, Fintype (ι i)] [∀ k, DecidableEq (β k)]

/-- **One step of the TT projector-splitting integrator** (Lubich–Oseledets–Vandereycken, arXiv
1407.2042, §4; the one-site TDVP sweep, arXiv 2603.13990, Eqs. (4.29)–(4.30)), from `Y₀` in form
(I) (right-orthogonal old cores `B i`, `i ≥ 1`): for `k < d` the forward K-substep
`YK k' = P_{≤k} P_{>k+1} F(t, YK k)`, for `k + 1 < d` the QR step (`kCap`, the new left core
`A k` spans `YK k t₁`) and the backward substep `YS k' = -P_{≤k+1} P_{>k+1} F(t, YS k)`, started
from the end values of the previous substep. The new approximation is `YK (d - 1) t₁`. -/
structure IsTTKSLStep (F : ℝ → Tensor ι → Tensor ι) (A B : TTCores ι β) (t₀ t₁ : ℝ)
    (Y₀ : Tensor ι) (YK YS : ℕ → ℝ → Tensor ι) : Prop where
  leftOrth : ∀ i : Fin d, i.val + 1 < d → IsLeftOrth A i
  rightOrth : ∀ i : Fin d, 0 < i.val → IsRightOrth B i
  start : ttRightProj B 1 Y₀ = Y₀
  kSol : ∀ k < d, ODESolution (fun t x => ttKProj A B k (F t x)) (YK k) t₀ t₁
  kStart₀ : YK 0 t₀ = Y₀
  kCap : ∀ k, k + 1 < d → ttLeftProj A (k + 1) (YK k t₁) = YK k t₁
  sSol : ∀ k, k + 1 < d → ODESolution (fun t x => -ttSProj A B k (F t x)) (YS k) t₀ t₁
  sStart : ∀ k, k + 1 < d → YS k t₀ = YK k t₁
  kStart : ∀ k, k + 1 < d → YK (k + 1) t₀ = YS k t₁

namespace IsTTKSLStep

variable [Subsingleton (β 0)] [Subsingleton (β d)] {F : ℝ → Tensor ι → Tensor ι}
  {A B : TTCores ι β} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YK YS : ℕ → ℝ → Tensor ι}

omit [Subsingleton (β 0)] [Subsingleton (β d)] in
/-- The backward substep as a Galerkin equation for `-F`. -/
lemma sSol' (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) {k : ℕ} (hk : k + 1 < d) :
    ODESolution (fun t x => ttSProj A B k (-F t x)) (YS k) t₀ t₁ :=
  ⟨(hs.sSol k hk).cont, fun t ht => ((hs.sSol k hk).deriv t ht).congr_deriv (map_neg _ _).symm⟩

lemma projK (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) {k : ℕ} (hk : k < d) :
    IsOrthProj (ttKProj A B k) :=
  isOrthProj_ttKProj hk (fun i hi => hs.leftOrth i (by omega))
    fun i hi => hs.rightOrth i (by omega)

lemma projS (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) {k : ℕ} (hk : k + 1 < d) :
    IsOrthProj (ttSProj A B k) :=
  isOrthProj_ttSProj hk.le (fun i hi => hs.leftOrth i (by omega))
    fun i hi => hs.rightOrth i (by omega)

/-- Every forward substep starts in the range of its projector. -/
theorem kStart_fix [Unique (β 0)] (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁) :
    ∀ k < d, ttKProj A B k (YK k t₀) = YK k t₀
  | 0, _ => by
    change ttLeftProj A 0 (ttRightProj B 1 (YK 0 t₀)) = YK 0 t₀
    rw [ttLeftProj_zero, hs.kStart₀, hs.start]
    rfl
  | k + 1, hk => by
    have hk' : k + 1 < d := hk
    have hK := (hs.kSol k (by omega)).galerkin_mem_range (hs.projK (by omega))
      (kStart_fix hs h01 k (by omega)) t₁ ⟨h01, le_rfl⟩
    have hS0 : ttSProj A B k (YS k t₀) = YS k t₀ := by
      rw [hs.sStart k hk']
      exact ttSProj_fix_of_ttKProj (by omega) (fun i hi => hs.rightOrth i (by omega)) hK
        (hs.kCap k hk')
    have hS := (hs.sSol' hk').galerkin_mem_range (hs.projS hk') hS0 t₁ ⟨h01, le_rfl⟩
    rw [hs.kStart k hk']
    exact ttKProj_succ_fix_of_ttSProj hk' (fun i hi => hs.leftOrth i (by omega))
      (fun i hi => hs.rightOrth i (by omega)) hS

/-- Every backward substep starts in the range of its projector. -/
theorem sStart_fix [Unique (β 0)] (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    {k : ℕ} (hk : k + 1 < d) : ttSProj A B k (YS k t₀) = YS k t₀ := by
  have hK := (hs.kSol k (by omega)).galerkin_mem_range (hs.projK (by omega))
    (hs.kStart_fix h01 k (by omega)) t₁ ⟨h01, le_rfl⟩
  rw [hs.sStart k hk]
  exact ttSProj_fix_of_ttKProj (by omega) (fun i hi => hs.rightOrth i (by omega)) hK (hs.kCap k hk)

/-- **Norm conservation of the TT projector-splitting integrator** (one-site TDVP; arXiv
2603.13990, §4.3, "The TDVP algorithm conserves both the norm and the energy", citing
Haegeman et al.): if `⟪F(t, x), x⟫ = 0` for all `x` (e.g. `F(t, x) = A x` with `A`
skew-symmetric, the real form of unitary dynamics), every substep conserves the norm, so
`‖Y₁‖ = ‖Y₀‖` for the new approximation `Y₁ = YK (d - 1) t₁`. -/
theorem norm_eq [Unique (β 0)] (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) : ∀ k < d, ‖YK k t₁‖ = ‖Y₀‖ := by
  intro k hk
  induction k with
  | zero =>
    rw [← hs.kStart₀]
    exact (hs.kSol 0 hk).galerkin_norm_eq' (hs.projK hk) (hs.kStart_fix h01 0 hk)
      (fun t x _ => hF t x) t₁ ⟨h01, le_rfl⟩
  | succ k ih =>
    have hk' : k + 1 < d := hk
    rw [(hs.kSol (k + 1) hk).galerkin_norm_eq' (hs.projK hk) (hs.kStart_fix h01 (k + 1) hk)
      (fun t x _ => hF t x) t₁ ⟨h01, le_rfl⟩, hs.kStart k hk',
      (hs.sSol' hk').galerkin_norm_eq' (hs.projS hk') (hs.sStart_fix h01 hk')
      (fun t x _ => by rw [inner_neg_left, hF, neg_zero]) t₁ ⟨h01, le_rfl⟩, hs.sStart k hk']
    exact ih (by omega)

/-- **Energy conservation of the TT projector-splitting integrator** (one-site TDVP; arXiv
2603.13990, §4.3): for `F(t, x) = J ∇ℰ(x)` with `J` skew (`⟪J z, z⟫ = 0`, e.g. the realified
`-i`) and commuting with all substep projectors, every substep conserves `ℰ`, so
`ℰ(Y₁) = ℰ(Y₀)` for the new approximation `Y₁ = YK (d - 1) t₁`. -/
theorem energy_eq (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) (h01 : t₀ ≤ t₁)
    {ℰ : Tensor ι → ℝ} {g : Tensor ι → Tensor ι} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {J : Tensor ι →L[ℝ] Tensor ι} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJK : ∀ k < d, ∀ z, J (ttKProj A B k z) = ttKProj A B k (J z))
    (hJS : ∀ k, k + 1 < d → ∀ z, J (ttSProj A B k z) = ttSProj A B k (J z))
    (hFJ : ∀ t x, F t x = J (g x)) : ∀ k < d, ℰ (YK k t₁) = ℰ Y₀ := by
  intro k hk
  induction k with
  | zero =>
    rw [← hs.kStart₀]
    exact (hs.kSol 0 hk).galerkin_energy_eq_of_skew (hs.projK hk) hℰ hJ (hJK 0 hk) hFJ t₁
      ⟨h01, le_rfl⟩
  | succ k ih =>
    have hk' : k + 1 < d := hk
    rw [(hs.kSol (k + 1) hk).galerkin_energy_eq_of_skew (hs.projK hk) hℰ hJ (hJK (k + 1) hk) hFJ
      t₁ ⟨h01, le_rfl⟩, hs.kStart k hk',
      (hs.sSol' hk').galerkin_energy_eq_of_skew (hs.projS hk') hℰ (J := -J)
        (fun z => by rw [_root_.neg_apply, inner_neg_left, hJ, neg_zero])
        (fun z => by rw [_root_.neg_apply, _root_.neg_apply, map_neg,
          hJS k hk' z])
        (fun t x => by rw [hFJ, _root_.neg_apply]) t₁ ⟨h01, le_rfl⟩,
      hs.sStart k hk']
    exact ih (by omega)

end IsTTKSLStep

/-- **For two modes the TT projector-splitting step is the matrix KSL step** (arXiv 1407.2042:
the TT integrator reduces to the matrix projector-splitting integrator of Lubich–Oseledets for
`d = 2`): the forward substep of core `0` is the K-step with `Q₀ = P_{>1}`, the backward substep
is the S-step and the forward substep of core `1` is the L-step with `P₁ = P_{≤1}`. Hence the
robust local error bound `IsKSLStep.local_error` applies. -/
theorem IsTTKSLStep.isKSLStep {ι : Fin 2 → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*}
    [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)] [Unique (β 0)] [Unique (β 2)]
    {F : ℝ → Tensor ι → Tensor ι} {A B : TTCores ι β} {t₀ t₁ : ℝ} {Y₀ : Tensor ι}
    {YK YS : ℕ → ℝ → Tensor ι} (hs : IsTTKSLStep F A B t₀ t₁ Y₀ YK YS) {ε : ℝ}
    (hε : ∀ t ∈ Icc t₀ t₁,
      ‖(1 - ttLeftProj A 1) ((1 - ttRightProj B 1) (F t (YK 0 t₁)))‖ ≤ ε) :
    IsKSLStep F ε (ttLeftProj A 1) (ttRightProj B 1) t₀ t₁ Y₀ (YK 0) (YS 0) (YK 1) where
  projP₁ := isOrthProj_ttLeftProj (by norm_num) fun i hi => hs.leftOrth i (by omega)
  projQ₀ := isOrthProj_ttRightProj (by norm_num) fun i hi => hs.rightOrth i (by omega)
  kSol := by
    have e : (fun t x => ttKProj A B 0 (F t x)) = fun t x => ttRightProj B 1 (F t x) := by
      funext t x
      change ttLeftProj A 0 (ttRightProj B 1 (F t x)) = _
      rw [ttLeftProj_zero]
      rfl
    exact e ▸ hs.kSol 0 (by norm_num)
  kStart := hs.kStart₀
  kCap := hs.kCap 0 (by norm_num)
  kNormal := hε
  sSol := hs.sSol 0 (by norm_num)
  sStart := hs.sStart 0 (by norm_num)
  lSol := by
    have e : (fun t x => ttKProj A B 1 (F t x)) = fun t x => ttLeftProj A 1 (F t x) := by
      funext t x
      change ttLeftProj A 1 (ttRightProj B 2 (F t x)) = _
      rw [ttRightProj_self]
      rfl
    exact e ▸ hs.kSol 1 (by norm_num)
  lStart := hs.kStart 0 (by norm_num)

end Continuous

/-! ### Examples -/

/-- The cores `C(α, x, α') = [x = 0]` on two modes of size two with one-element bonds (the
tensor train `e₀ ⊗ e₀`). -/
private noncomputable def exCores : TTCores (fun _ : Fin 2 => Fin 2) (fun _ => Unit) :=
  fun _ _ x _ => if x = 0 then 1 else 0

private lemma exCores_left (i : Fin 2) : IsLeftOrth exCores i := fun b b' => by
  change ∑ _a : Unit, ∑ x : Fin 2, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix Unit Unit ℝ) b b'
  simp

private lemma exCores_right (i : Fin 2) : IsRightOrth exCores i := fun a a' => by
  change ∑ x : Fin 2, ∑ _b : Unit, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix Unit Unit ℝ) a a'
  simp

/-- Non-vacuity of `IsTTKSLStep`: the zero field and constant trajectories at `Y₀ = tt C` for the
left- and right-orthogonal cores `exCores` form a TT projector-splitting step. -/
example : IsTTKSLStep (fun _ _ => 0) exCores exCores 0 1 (tt exCores) (fun _ _ => tt exCores)
    (fun _ _ => tt exCores) := by
  refine ⟨fun i _ => exCores_left i, fun i _ => exCores_right i,
    ttRightProj_tt (by norm_num) fun i _ => exCores_right i, fun k _ => ?_, rfl,
    fun k _ => ttLeftProj_tt (by omega) fun i _ => exCores_left i, fun k _ => ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · exact ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t _ _⟩
  · exact ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t _ _⟩

end LeanDLRA.Tensor

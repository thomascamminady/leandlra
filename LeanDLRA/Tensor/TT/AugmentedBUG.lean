import LeanDLRA.Tensor.TT.ProjectorSplitting
import LeanDLRA.Integrators.RankAdaptiveBUG

/-!
# The augmented BUG integrator for tensor trains (MPS-BUG)

The augmented (rank-adaptive) basis-update & Galerkin integrator for tensor trains / matrix
product states (Ceruti–Lubich–Sulz for tree tensor networks; formulated for MPS by
Kapás–Sulz–Verhoeven–Werner–Legeza–Lubich, arXiv 2609.12848, §II B, and by
Petersson–Hodges-Heilmann–Günther, arXiv 2603.13990, §5.2) keeps the orthogonality centre at a
fixed bond (or site) and performs one step in three parts:

1. **left sweep**: for the cores `i < n` from left to right, a K-step
   `Y' = P̂_{≤i} P_{>i+1} F(t, Y)` (left interface of the new augmented cores `Ah`, right interface
   of the old right-orthogonal cores `B`; arXiv 2609.12848, Eqs. (6)–(10); arXiv 2603.13990,
   Eq. (5.10)) started from the old state in the new basis, `P̂_{≤i} Y₀`, followed by the
   augmented QR decomposition: the new core `Ah i` spans the K-step values at `t₀` and `t₁`; the
   **right sweep** is the mirror image (Eq. (5.11) of arXiv 2603.13990);
2. a **Galerkin step** in the space of tensor trains with the augmented left interface `X̂_{≤j}`
   and right interface `X̂_{>k}` (a bond matrix for `j = k`, arXiv 2609.12848; a centre core for
   `k = j + 1`, arXiv 2603.13990, Eq. (5.12)), started from the old state rotated into the new
   bases;
3. a **truncation** to a tolerance `ϑ`.

Every step goes forward in time; there is no backward substep (in contrast to the projector
splitting integrator `IsTTKSLStep`, whose forward substeps use the same projectors `ttKProj`).

## Main definitions

* `IsTTAugGalerkinStep`: the Galerkin step with truncation in the space of tensor trains with
  fixed augmented interfaces that contain the starting value.
* `IsTTAugLeftSweep`, `IsTTAugRightSweep`: the augmentation sweeps.
* `IsTTAugBUGStep`: one step of the augmented MPS-BUG integrator.
* `IsTTMidpointBUGStep`: the Galerkin part of the midpoint MPS-BUG integrator (arXiv 2609.12848,
  §II C), whose bases contain the bases at `t₀` and the predictor at the midpoint.

## Main results

* `IsTTAugGalerkinStep.toAugmentedGalerkinStep`: bridge to the abstract augmented Galerkin step
  `IsAugmentedGalerkinStep` (Ceruti–Kusch–Lubich, arXiv 2104.05247), with the orthogonal
  projector `R = P̂_{≤j} P̂_{>k}`.
* `IsTTAugGalerkinStep.start_eq`, `norm_eq`, `energy_eq`: the Galerkin step starts at `Y₀` and,
  in the absence of truncation, conserves the norm (`⟪F(t, x), x⟫ = 0`) and the energy
  (`F = J ∇ℰ` with `J` skew and commuting with `R`); with truncation both change by at most
  `ϑ`, resp. `β ϑ`.
* `IsTTAugGalerkinStep.eq_ttBond`, `eq_tt_update`: the Galerkin solution is a tensor train with
  the augmented interfaces and a bond matrix (`j = k`) or a centre core (`k = j + 1`).
* `IsTTAugLeftSweep.augL`, `IsTTAugRightSweep.augR`: the augmented interfaces contain the old
  state, `P̂_{≤n} Y₀ = Y₀`, `P̂_{>m} Y₀ = Y₀`.
* `IsTTAugBUGStep.toTTAugGalerkinStep`, `IsTTAugBUGStep.norm_eq`, `IsTTAugBUGStep.energy_eq`:
  **the augmented MPS-BUG integrator conserves norm and energy in the absence of truncation**
  (arXiv 2609.12848, §I: "further preserve norm and energy for unitary dynamics in the absence
  of truncation"), and `IsTTMidpointBUGStep.norm_eq`, `energy_eq` for the midpoint variant.

Everything is real. Complex MPS (quantum states) are covered only through the abstract
realification of `IsAugmentedGalerkinStep` (the complex structure `J = -i` is skew and commutes
with complex-linear projectors); the real TT projectors of this file do not act on a complex
structure, so the energy statements carry the commutation `J R = R J` as a hypothesis.
-/

open scoped Matrix RealInnerProductSpace
open Set

namespace LeanDLRA.Tensor

variable {d : ℕ} {ι : Fin d → Type*} [∀ i, Fintype (ι i)] {β : ℕ → Type*} [∀ k, Fintype (β k)]
  [∀ k, DecidableEq (β k)]

/-! ### The Galerkin step in the augmented bases -/

/-- **Galerkin step of the augmented MPS-BUG integrator with truncation**: in the space of tensor
trains with the left interface of the augmented left-orthogonal cores `A` (cores `< j`) and the
right interface of the augmented right-orthogonal cores `B` (cores `≥ k`), `j ≤ k ≤ d`, which
contain the starting value (`augL`, `augR`), the Galerkin equation
`YS' = P̂_{≤j} P̂_{>k} F(t, YS)` from `YS t₀ = P̂_{≤j} P̂_{>k} Y₀` (the old core rotated into the
new bases, arXiv 2609.12848, Fig. 2e) followed by a truncation `‖Y₁ - YS t₁‖ ≤ ϑ`
(arXiv 2609.12848, Eqs. (11)–(12)). -/
structure IsTTAugGalerkinStep (F : ℝ → Tensor ι → Tensor ι) (ϑ : ℝ) (A B : TTCores ι β)
    (j k : ℕ) (t₀ t₁ : ℝ) (Y₀ : Tensor ι) (YS : ℝ → Tensor ι) (Y₁ : Tensor ι) : Prop where
  le : j ≤ k
  le_d : k ≤ d
  leftOrth : ∀ i : Fin d, i.val < j → IsLeftOrth A i
  rightOrth : ∀ i : Fin d, k ≤ i.val → IsRightOrth B i
  /-- The augmented left interface contains the old state. -/
  augL : ttLeftProj A j Y₀ = Y₀
  /-- The augmented right interface contains the old state. -/
  augR : ttRightProj B k Y₀ = Y₀
  sSol : ODESolution (fun t x => ttLeftProj A j (ttRightProj B k (F t x))) YS t₀ t₁
  sStart : YS t₀ = ttLeftProj A j (ttRightProj B k Y₀)
  trunc : ‖Y₁ - YS t₁‖ ≤ ϑ

namespace IsTTAugGalerkinStep

variable [Subsingleton (β 0)] [Subsingleton (β d)] {F : ℝ → Tensor ι → Tensor ι} {ϑ : ℝ}
  {A B : TTCores ι β} {j k : ℕ} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YS : ℝ → Tensor ι} {Y₁ : Tensor ι}

/-- The Galerkin projector `P̂_{≤j} P̂_{>k}` is an orthogonal projector. -/
theorem proj (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) :
    IsOrthProj (ttLeftProj A j * ttRightProj B k) :=
  isOrthProj_ttLeftProj_mul_ttRightProj hs.le hs.le_d hs.leftOrth hs.rightOrth

/-- **Bridge to the abstract augmented Galerkin step** (arXiv 2104.05247, §3): the TT Galerkin
step is an `IsAugmentedGalerkinStep` with `R = P̂_{≤j} P̂_{>k}`. -/
theorem toAugmentedGalerkinStep (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) :
    IsAugmentedGalerkinStep F ϑ (ttLeftProj A j * ttRightProj B k) t₀ t₁ Y₀ YS Y₁ where
  proj := hs.proj
  fix := by
    change ttLeftProj A j (ttRightProj B k Y₀) = Y₀
    rw [hs.augR, hs.augL]
  sSol := hs.sSol
  sStart := hs.sStart
  trunc := hs.trunc

/-- The Galerkin step starts exactly at the old state (Lemma 1 of arXiv 2104.05247 for MPS; the
rotation of the core into the augmented bases is exact, arXiv 2609.12848, Fig. 2e). -/
theorem start_eq (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) : YS t₀ = Y₀ :=
  hs.toAugmentedGalerkinStep.start_eq

/-- **Norm conservation of the augmented MPS-BUG Galerkin step** (arXiv 2609.12848, §I; arXiv
2104.05247, Thm 4): if `⟪F(t, x), x⟫ = 0` (e.g. `F(t, x) = A x` with `A` skew-symmetric, the real
form of unitary dynamics), then `‖YS t₁‖ = ‖Y₀‖` before the truncation and
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ` after it. -/
theorem norm_eq (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ ∧ |‖Y₁‖ - ‖Y₀‖| ≤ ϑ :=
  hs.toAugmentedGalerkinStep.abs_norm_sub_le h01 fun t x _ => hF t x

/-- **Energy conservation of the augmented MPS-BUG Galerkin step** (arXiv 2609.12848, §I; arXiv
2104.05247, Thms 6–7): for `F = J ∇ℰ` with `J` skew and commuting with the Galerkin projector,
`ℰ(YS t₁) = ℰ(Y₀)` before the truncation and `|ℰ(Y₁) - ℰ(Y₀)| ≤ β ϑ` after it, if `‖∇ℰ‖ ≤ β` on
the segment `[YS t₁, Y₁]`. -/
theorem energy_eq (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) (h01 : t₀ ≤ t₁)
    {ℰ : Tensor ι → ℝ} {g : Tensor ι → Tensor ι} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {J : Tensor ι →L[ℝ] Tensor ι} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJR : ∀ z, J (ttLeftProj A j (ttRightProj B k z)) = ttLeftProj A j (ttRightProj B k (J z)))
    (hFJ : ∀ t x, F t x = J (g x)) {β' : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β') :
    ℰ (YS t₁) = ℰ Y₀ ∧ |ℰ Y₁ - ℰ Y₀| ≤ β' * ϑ :=
  hs.toAugmentedGalerkinStep.energy_sub_le_of_skew h01 hℰ hJ hJR hFJ hβ

/-- The Galerkin solution stays in the Galerkin space. -/
theorem mem_range (hs : IsTTAugGalerkinStep F ϑ A B j k t₀ t₁ Y₀ YS Y₁) :
    ∀ t ∈ Icc t₀ t₁, ttLeftProj A j (ttRightProj B k (YS t)) = YS t :=
  hs.sSol.galerkin_mem_range hs.proj (by
    change ttLeftProj A j (ttRightProj B k (YS t₀)) = YS t₀
    rw [hs.start_eq, hs.augR, hs.augL])

/-- **Bond-centred Galerkin step** (arXiv 2609.12848, §II B): for `j = k` the Galerkin solution
is the bond-centred tensor train `X̂_{≤j} S(t) X̂_{>j}ᵀ` with the augmented interfaces and the bond
matrix `S(t) = X̂_{≤j}ᵀ YS(t)⟨j⟩ X̂_{>j}` (of size up to `2M × 2M`). -/
theorem eq_ttBond (hs : IsTTAugGalerkinStep F ϑ A B j j t₀ t₁ Y₀ YS Y₁) :
    ∀ t ∈ Icc t₀ t₁, YS t = ttBond A B j (ttBondCoeff A B j (YS t)) := fun t ht => by
  rw [ttBond_ttBondCoeff, hs.mem_range t ht]

/-- **Site-centred Galerkin step** (arXiv 2603.13990, Eq. (5.12)): for `k = j + 1` the Galerkin
solution is the tensor train with the augmented left cores before `j`, the centre core
`M(t) = ttCoreCoeff A B j (YS t)` and the augmented right cores after `j`. -/
theorem eq_tt_update (hs : IsTTAugGalerkinStep F ϑ A B j (j + 1) t₀ t₁ Y₀ YS Y₁) (hj : j < d) :
    ∀ t ∈ Icc t₀ t₁,
      YS t = tt (Function.update (ttMix A B j) ⟨j, hj⟩ (ttCoreCoeff A B j hj (YS t))) :=
  fun t ht => by rw [tt_update_ttCoreCoeff, hs.mem_range t ht]

end IsTTAugGalerkinStep

/-! ### The augmentation sweeps -/

/-- **Left augmentation sweep of the MPS-BUG integrator** (arXiv 2609.12848, Eqs. (6)–(10);
arXiv 2603.13990, Eq. (5.10)) over the cores `i < n`: the old state `Y₀` is in right-orthonormal
form (`P_{>1} Y₀ = Y₀` for the right-orthogonal cores `B i`, `i ≥ 1`, after the RQ sweep (5)), the
K-step of core `i` solves `YK i' = P̂_{≤i} P_{>i+1} F(t, YK i)` from the old state in the new
basis, `YK i t₀ = P̂_{≤i} Y₀`, and the augmented QR step makes the new left-orthogonal core
`A i` span both `YK i t₀` and `YK i t₁` (`K̃ = [K(t₀), K(t₁)]`, Eq. (8)). -/
structure IsTTAugLeftSweep (F : ℝ → Tensor ι → Tensor ι) (A B : TTCores ι β) (n : ℕ)
    (t₀ t₁ : ℝ) (Y₀ : Tensor ι) (YK : ℕ → ℝ → Tensor ι) : Prop where
  le_d : n ≤ d
  leftOrth : ∀ i : Fin d, i.val < n → IsLeftOrth A i
  rightOrth : ∀ i : Fin d, 0 < i.val → IsRightOrth B i
  start : ttRightProj B 1 Y₀ = Y₀
  kSol : ∀ i < n, ODESolution (fun t x => ttKProj A B i (F t x)) (YK i) t₀ t₁
  kStart : ∀ i < n, YK i t₀ = ttLeftProj A i Y₀
  capStart : ∀ i < n, ttLeftProj A (i + 1) (YK i t₀) = YK i t₀
  capEnd : ∀ i < n, ttLeftProj A (i + 1) (YK i t₁) = YK i t₁

/-- **Right augmentation sweep of the MPS-BUG integrator** (the mirror image of the left sweep;
arXiv 2603.13990, Eq. (5.11)) over the cores `i ≥ m`: the old state is in left-orthonormal form
(left-orthogonal cores `A i`, `i < d - 1`), the K-step of core `i` solves
`YL i' = P_{≤i} P̂_{>i+1} F(t, YL i)` from `P̂_{>i+1} Y₀`, and the new right-orthogonal core `B i`
spans `YL i t₀` and `YL i t₁`. -/
structure IsTTAugRightSweep (F : ℝ → Tensor ι → Tensor ι) (A B : TTCores ι β) (m : ℕ)
    (t₀ t₁ : ℝ) (Y₀ : Tensor ι) (YL : ℕ → ℝ → Tensor ι) : Prop where
  le_d : m ≤ d
  leftOrth : ∀ i : Fin d, i.val + 1 < d → IsLeftOrth A i
  rightOrth : ∀ i : Fin d, m ≤ i.val → IsRightOrth B i
  start : ttLeftProj A (d - 1) Y₀ = Y₀
  lSol : ∀ i, m ≤ i → i < d → ODESolution (fun t x => ttKProj A B i (F t x)) (YL i) t₀ t₁
  lStart : ∀ i, m ≤ i → i < d → YL i t₀ = ttRightProj B (i + 1) Y₀
  capStart : ∀ i, m ≤ i → i < d → ttRightProj B i (YL i t₀) = YL i t₀
  capEnd : ∀ i, m ≤ i → i < d → ttRightProj B i (YL i t₁) = YL i t₁

/-- **The augmented left interfaces contain the old state**: `P̂_{≤i} Y₀ = Y₀` for `i ≤ n`, so
every K-step starts at the old state (`YK i t₀ = Y₀`). -/
theorem IsTTAugLeftSweep.augL [Unique (β 0)] {F : ℝ → Tensor ι → Tensor ι} {A B : TTCores ι β}
    {n : ℕ} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YK : ℕ → ℝ → Tensor ι}
    (hs : IsTTAugLeftSweep F A B n t₀ t₁ Y₀ YK) : ∀ i ≤ n, ttLeftProj A i Y₀ = Y₀
  | 0, _ => by rw [ttLeftProj_zero]; rfl
  | i + 1, hi => by
    have h := hs.capStart i hi
    rw [hs.kStart i hi, hs.augL i (by omega)] at h
    exact h

/-- Every K-step of the left sweep starts at the old state. -/
theorem IsTTAugLeftSweep.kStart_eq [Unique (β 0)] {F : ℝ → Tensor ι → Tensor ι}
    {A B : TTCores ι β} {n : ℕ} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YK : ℕ → ℝ → Tensor ι}
    (hs : IsTTAugLeftSweep F A B n t₀ t₁ Y₀ YK) {i : ℕ} (hi : i < n) : YK i t₀ = Y₀ := by
  rw [hs.kStart i hi, hs.augL i hi.le]

/-- **The augmented right interfaces contain the old state**: `P̂_{>i} Y₀ = Y₀` for
`m ≤ i ≤ d`. -/
theorem IsTTAugRightSweep.augR [Unique (β d)] {F : ℝ → Tensor ι → Tensor ι} {A B : TTCores ι β}
    {m : ℕ} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YL : ℕ → ℝ → Tensor ι}
    (hs : IsTTAugRightSweep F A B m t₀ t₁ Y₀ YL) (i : ℕ) (hmi : m ≤ i) (hid : i ≤ d) :
    ttRightProj B i Y₀ = Y₀ := by
  induction hn : d - i generalizing i with
  | zero =>
    obtain rfl : i = d := by omega
    rw [ttRightProj_self]
    rfl
  | succ n ih =>
    have h := hs.capStart i hmi (by omega)
    rw [hs.lStart i hmi (by omega), ih (i + 1) (by omega) (by omega) (by omega)] at h
    exact h

/-! ### One step of the augmented MPS-BUG integrator -/

/-- **One step of the augmented MPS-BUG integrator** (arXiv 2609.12848, §II B, with `m = n`, a
bond-centred Galerkin step; arXiv 2603.13990, §5.2, with `m = n + 1`, a site-centred one): a
left sweep producing the augmented left cores `Ah` (from the right-orthonormal form `B` of `Y₀`),
a right sweep producing the augmented right cores `Bh` (from the left-orthonormal form `A` of
`Y₀`), the Galerkin step in the augmented bases and a truncation. -/
structure IsTTAugBUGStep (F : ℝ → Tensor ι → Tensor ι) (ϑ : ℝ) (A B Ah Bh : TTCores ι β)
    (n m : ℕ) (t₀ t₁ : ℝ) (Y₀ : Tensor ι) (YK YL : ℕ → ℝ → Tensor ι) (YS : ℝ → Tensor ι)
    (Y₁ : Tensor ι) : Prop where
  left : IsTTAugLeftSweep F Ah B n t₀ t₁ Y₀ YK
  right : IsTTAugRightSweep F A Bh m t₀ t₁ Y₀ YL
  le : n ≤ m
  sSol : ODESolution (fun t x => ttLeftProj Ah n (ttRightProj Bh m (F t x))) YS t₀ t₁
  sStart : YS t₀ = ttLeftProj Ah n (ttRightProj Bh m Y₀)
  trunc : ‖Y₁ - YS t₁‖ ≤ ϑ

namespace IsTTAugBUGStep

variable [Unique (β 0)] [Unique (β d)] {F : ℝ → Tensor ι → Tensor ι} {ϑ : ℝ}
  {A B Ah Bh : TTCores ι β} {n m : ℕ} {t₀ t₁ : ℝ} {Y₀ : Tensor ι} {YK YL : ℕ → ℝ → Tensor ι}
  {YS : ℝ → Tensor ι} {Y₁ : Tensor ι}

/-- The Galerkin part of an augmented MPS-BUG step is an augmented TT Galerkin step: the
augmentation sweeps guarantee that the new bases contain the old state. -/
theorem toTTAugGalerkinStep (hs : IsTTAugBUGStep F ϑ A B Ah Bh n m t₀ t₁ Y₀ YK YL YS Y₁) :
    IsTTAugGalerkinStep F ϑ Ah Bh n m t₀ t₁ Y₀ YS Y₁ where
  le := hs.le
  le_d := hs.right.le_d
  leftOrth := hs.left.leftOrth
  rightOrth := hs.right.rightOrth
  augL := hs.left.augL n le_rfl
  augR := hs.right.augR m le_rfl hs.right.le_d
  sSol := hs.sSol
  sStart := hs.sStart
  trunc := hs.trunc

/-- **The augmented MPS-BUG integrator conserves the norm in the absence of truncation**
(arXiv 2609.12848, §I and §II B): for `⟪F(t, x), x⟫ = 0`, `‖YS t₁‖ = ‖Y₀‖` and
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`. -/
theorem norm_eq (hs : IsTTAugBUGStep F ϑ A B Ah Bh n m t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ ∧ |‖Y₁‖ - ‖Y₀‖| ≤ ϑ :=
  hs.toTTAugGalerkinStep.norm_eq h01 hF

/-- **The augmented MPS-BUG integrator conserves the energy in the absence of truncation**
(arXiv 2609.12848, §I): for `F = J ∇ℰ` with `J` skew and commuting with the Galerkin projector,
`ℰ(YS t₁) = ℰ(Y₀)` and `|ℰ(Y₁) - ℰ(Y₀)| ≤ β ϑ` if `‖∇ℰ‖ ≤ β` on `[YS t₁, Y₁]`. -/
theorem energy_eq (hs : IsTTAugBUGStep F ϑ A B Ah Bh n m t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    {ℰ : Tensor ι → ℝ} {g : Tensor ι → Tensor ι} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {J : Tensor ι →L[ℝ] Tensor ι} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJR : ∀ z, J (ttLeftProj Ah n (ttRightProj Bh m z)) = ttLeftProj Ah n (ttRightProj Bh m (J z)))
    (hFJ : ∀ t x, F t x = J (g x)) {β' : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β') :
    ℰ (YS t₁) = ℰ Y₀ ∧ |ℰ Y₁ - ℰ Y₀| ≤ β' * ϑ :=
  hs.toTTAugGalerkinStep.energy_eq h01 hℰ hJ hJR hFJ hβ

end IsTTAugBUGStep

/-! ### The midpoint MPS-BUG integrator -/

/-- **The Galerkin part of the midpoint MPS-BUG integrator** (arXiv 2609.12848, §II C, steps
(iii)–(iv)): the Galerkin step over the full interval from `t₀`, in bases of up to four times the
bond dimension that contain the bases at `t₀` (`augL`, `augR` of the Galerkin step) and the
predictor `Yh` at the midpoint (`midL`, `midR`). In the paper `Yh` is the untruncated augmented
BUG half step (step (i)); it enters here only through the capture conditions, which is all that
the conservation properties use. -/
structure IsTTMidpointBUGStep (F : ℝ → Tensor ι → Tensor ι) (ϑ : ℝ) (A B : TTCores ι β)
    (n m : ℕ) (t₀ t₁ : ℝ) (Y₀ Yh : Tensor ι) (YS : ℝ → Tensor ι) (Y₁ : Tensor ι) : Prop
    extends IsTTAugGalerkinStep F ϑ A B n m t₀ t₁ Y₀ YS Y₁ where
  midL : ttLeftProj A n Yh = Yh
  midR : ttRightProj B m Yh = Yh

namespace IsTTMidpointBUGStep

variable [Subsingleton (β 0)] [Subsingleton (β d)] {F : ℝ → Tensor ι → Tensor ι} {ϑ : ℝ}
  {A B : TTCores ι β} {n m : ℕ} {t₀ t₁ : ℝ} {Y₀ Yh : Tensor ι} {YS : ℝ → Tensor ι}
  {Y₁ : Tensor ι}

/-- **The midpoint MPS-BUG integrator conserves the norm in the absence of truncation**
(arXiv 2609.12848, §I). -/
theorem norm_eq (hs : IsTTMidpointBUGStep F ϑ A B n m t₀ t₁ Y₀ Yh YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ ∧ |‖Y₁‖ - ‖Y₀‖| ≤ ϑ :=
  hs.toIsTTAugGalerkinStep.norm_eq h01 hF

/-- **The midpoint MPS-BUG integrator conserves the energy in the absence of truncation**
(arXiv 2609.12848, §I). -/
theorem energy_eq (hs : IsTTMidpointBUGStep F ϑ A B n m t₀ t₁ Y₀ Yh YS Y₁) (h01 : t₀ ≤ t₁)
    {ℰ : Tensor ι → ℝ} {g : Tensor ι → Tensor ι} (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    {J : Tensor ι →L[ℝ] Tensor ι} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJR : ∀ z, J (ttLeftProj A n (ttRightProj B m z)) = ttLeftProj A n (ttRightProj B m (J z)))
    (hFJ : ∀ t x, F t x = J (g x)) {β' : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β') :
    ℰ (YS t₁) = ℰ Y₀ ∧ |ℰ Y₁ - ℰ Y₀| ≤ β' * ϑ :=
  hs.toIsTTAugGalerkinStep.energy_eq h01 hℰ hJ hJR hFJ hβ

end IsTTMidpointBUGStep

/-! ### Examples -/

/-- The cores `C(α, x, α') = [x = 0]` on two modes of size two with one-element bonds. -/
private noncomputable def augC : TTCores (fun _ : Fin 2 => Fin 2) (fun _ => Unit) :=
  fun _ _ x _ => if x = 0 then 1 else 0

private lemma augC_left (i : Fin 2) : IsLeftOrth augC i := fun b b' => by
  change ∑ _a : Unit, ∑ x : Fin 2, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix Unit Unit ℝ) b b'
  simp

private lemma augC_right (i : Fin 2) : IsRightOrth augC i := fun a a' => by
  change ∑ x : Fin 2, ∑ _b : Unit, (if x = 0 then (1 : ℝ) else 0) * (if x = 0 then 1 else 0) =
    (1 : Matrix Unit Unit ℝ) a a'
  simp

/-- Non-vacuity of `IsTTAugBUGStep`: for the zero field, constant trajectories at the tensor
train `Y₀ = tt C` of the cores `augC` (as old and new cores, bond-centred at `n = m = 1`) form
an augmented MPS-BUG step without truncation. -/
example : IsTTAugBUGStep (fun _ _ => 0) 0 augC augC augC augC 1 1 0 1 (tt augC)
    (fun _ _ => tt augC) (fun _ _ => tt augC) (fun _ => tt augC) (tt augC) := by
  have hc : ∀ (P : Tensor (fun _ : Fin 2 => Fin 2) →L[ℝ] Tensor (fun _ : Fin 2 => Fin 2)),
      ODESolution (fun _ x => P ((fun _ _ => 0 : ℝ → Tensor (fun _ : Fin 2 => Fin 2) →
        Tensor (fun _ : Fin 2 => Fin 2)) 0 x)) (fun _ => tt augC) 0 1 := fun P =>
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t _ _⟩
  have hL : ∀ k ≤ 2, ttLeftProj augC k (tt augC) = tt augC := fun k hk =>
    ttLeftProj_tt hk fun i _ => augC_left i
  have hR : ∀ k ≤ 2, ttRightProj augC k (tt augC) = tt augC := fun k hk =>
    ttRightProj_tt hk fun i _ => augC_right i
  have hS : ODESolution (fun _ x => ttLeftProj augC 1 (ttRightProj augC 1
      ((fun _ _ => 0 : ℝ → Tensor (fun _ : Fin 2 => Fin 2) → Tensor (fun _ : Fin 2 => Fin 2))
        0 x))) (fun _ => tt augC) 0 1 :=
    ⟨continuousOn_const, fun t _ => by simpa using hasDerivWithinAt_const t _ _⟩
  have hS0 : tt augC = ttLeftProj augC 1 (ttRightProj augC 1 (tt augC)) := by
    rw [hR 1 (by norm_num), hL 1 (by norm_num)]
  exact ⟨⟨by norm_num, fun i _ => augC_left i, fun i _ => augC_right i,
      hR 1 (by norm_num), fun i _ => hc _, fun i hi => (hL i (by omega)).symm,
      fun i hi => hL _ (by omega), fun i hi => hL _ (by omega)⟩,
    ⟨by norm_num, fun i _ => augC_left i, fun i _ => augC_right i, hL _ (by norm_num),
      fun i _ _ => hc _, fun i _ hi => (hR _ (by omega)).symm, fun i _ hi => hR _ (by omega),
      fun i _ hi => hR _ (by omega)⟩, le_rfl, hS, hS0, by simp⟩

end LeanDLRA.Tensor

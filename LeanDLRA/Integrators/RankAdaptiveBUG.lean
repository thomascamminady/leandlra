import LeanDLRA.Integrators.BUG
import LeanDLRA.Foundations.Galerkin

/-!
# The rank-adaptive (augmented) BUG integrator

This file formalises the rank-adaptive robust integrator of Ceruti–Kusch–Lubich,
*A rank-adaptive robust integrator for dynamical low-rank approximation*
(BIT 2022, [CerutiKuschLubich2022]), in the abstract projector framework of the library.

## The algorithm ([CerutiKuschLubich2022, §2.1]) as full-space trajectories

One step from `Y₀ = U₀ S₀ V₀ᵀ` (rank `r`) at `t₀` to `t₁ = t₀ + h`:

1. **K-step** `K' = F(t, K V₀ᵀ) V₀`, `K(t₀) = U₀ S₀`, and **L-step**
   `L' = F(t, U₀ Lᵀ)ᵀ U₀`, `L(t₀) = V₀ S₀ᵀ` (as for the BUG integrator); the **augmented bases**
   `Û ∈ ℝ^{m×2r}`, `V̂ ∈ ℝ^{n×2r}` are orthonormal bases of the ranges of `(K(t₁), U₀)` and
   `(L(t₁), V₀)`;
2. **Galerkin S-step** `Ŝ' = Ûᵀ F(t, Û Ŝ V̂ᵀ) V̂`, `Ŝ(t₀) = M̂ S₀ N̂ᵀ` with `M̂ = Ûᵀ U₀`,
   `N̂ = V̂ᵀ V₀` (eq. (5)), giving the rank-`2r` approximation `Ŷ₁ = Û Ŝ(t₁) V̂ᵀ` (eq. (7));
3. **truncation** of `Ŝ(t₁)` by an SVD to the tolerance `ϑ`, giving `Y₁ = U₁ S₁ V₁ᵀ` with
   `‖Y₁ - Ŷ₁‖ ≤ ϑ` (eq. (6)).

Abstractly, on a real inner product space `E` with orthogonal projectors (`P₀ X = U₀ U₀ᵀ X`,
`Q₀ X = X V₀ V₀ᵀ` and the **augmented** projectors `P₁ X = Û Ûᵀ X`, `Q₁ X = X V̂ V̂ᵀ`):

* K-step `YK' = Q₀ F(t, YK)`, `YK t₀ = Y₀`, and `P₁ (YK t₁) = YK t₁` (`Û` spans `K(t₁)`);
* L-step `YL' = P₀ F(t, YL)`, `YL t₀ = Y₀`, and `Q₁ (YL t₁) = YL t₁` (`V̂` spans `L(t₁)`);
* the augmentation: `P₁ Y₀ = Y₀` and `Q₁ Y₀ = Y₀` (`Û` spans `U₀`, `V̂` spans `V₀`; see
  `aug_fix_of_comp_eq` for the derivation from `Û Ûᵀ U₀ = U₀`);
* S-step `YS' = P₁ Q₁ F(t, YS)`, `YS t₀ = P₁ Q₁ Y₀` (the trajectory `YS = Û Ŝ V̂ᵀ`, since
  `Û M̂ S₀ N̂ᵀ V̂ᵀ = Û Ûᵀ Y₀ V̂ V̂ᵀ`), so that `Ŷ₁ = YS t₁`;
* truncation: `‖Y₁ - YS t₁‖ ≤ ϑ`.

Without the truncation this is exactly a BUG step (`IsBUGStep`) with the augmented projectors, so
all robust estimates of `Integrators/BUG.lean` apply; this is how the error analysis of the paper
"follows the lines of" Ceruti–Lubich.  All hypotheses are bundled in `IsRankAdaptiveBUGStep`.

## Main results

Numbering as in [CerutiKuschLubich2022].

* `IsRankAdaptiveBUGStep.start_eq` (**Lemma 1**): the Galerkin step starts at `Ŷ₀ = Y₀`;
  `galerkin_eqOn_iff`: the Galerkin S-step started at `R Y₀` (as in the algorithm) equals the
  Galerkin flow started at `Y₀` exactly when `Y₀ ∈ range R`, and otherwise the two stay
  `‖(1 - R) Y₀‖` apart (`norm_normal_le_galerkin_sub`); hence the rank-adaptive S-step is the
  Galerkin flow from `Y₀` (`IsRankAdaptiveBUGStep.eqOn_of_start`).
* `IsRankAdaptiveBUGStep.local_error`, `IsRankAdaptiveBUGStep.local_error_le`
  (local error, **Theorem 2**): with `ϑ_K = h (4 L B h + ε)`,
  `‖Y₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + 2ϑ_K) + 2ϑ_K + ϑ ≤ h (c₁ ε + c₂ h) + ϑ`.
* `rankAdaptiveBUG_global_error`, `rankAdaptiveBUG_global_error_le` (**Theorem 2**): for `n h ≤ T`,
  `‖Yₙ - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ n ϑ` with `c₀ = c₃ = e^{L T}`,
  `c₁ = T e^{L T} bugC₁ L H`, `c₂ = T e^{L T} bugC₂ L B H`; independent of singular values.
* `IsInexactRankAdaptiveBUGStep.local_error_le`, `rankAdaptiveBUG_inexact_global_error`,
  `rankAdaptiveBUG_inexact_global_error_le` (**remark after Theorem 2**, inexact substeps): if
  the K-, L- and S-step differential equations are solved only up to local errors `η` (the
  augmented bases spanning the *computed* `K₁`, `L₁`), the local error gains the term
  `(2 e^{L H} + 1) η` and the global error the term `c₃ n (2 e^{L H} + 1) η`, again with constants
  independent of singular values (`kstep_capture_approx`: capture by a basis of the computed K-step
  result); `IsInexactRankAdaptiveBUGStep.abs_norm_sub_le`: Theorem 4 with `ϑ + η`.
* `IsRankAdaptiveBUGStep.norm_untruncated_eq`, `IsRankAdaptiveBUGStep.abs_norm_sub_le`
  (**Theorem 4**): if `⟪F(t, Y), Y⟫ = 0` then `‖Ŷ₁‖ = ‖Y₀‖` and `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`,
  independently of `h`; `IsRankAdaptiveBUGStep.norm_sq_add_of_proj`: if the truncation is an
  orthogonal projection of `Ŷ₁` (as the truncated SVD is), then exactly
  `‖Y₁‖² + ‖Y₁ - Ŷ₁‖² = ‖Y₀‖²`; `rankAdaptiveBUG_norm_drift`: over `n` steps (arbitrary step
  sizes) `|‖Yₙ‖ - ‖Y₀‖| ≤ n ϑ`; dissipative version `IsRankAdaptiveBUGStep.norm_le_of_dissipative`.
* `IsRankAdaptiveBUGStep.energy_le` (**Theorem 5**, gradient systems `F = -∇f`):
  `f(Y₁) ≤ f(Y₀) - α² h + β ϑ`, with `α² ≤ ‖Û Ûᵀ ∇f(Ŷ(t)) V̂ V̂ᵀ‖²` and `‖∇f‖ ≤ β` on the segment
  `[Ŷ₁, Y₁]`; `IsRankAdaptiveBUGStep.energy_le_of_lipschitzOnWith` (`f` Lipschitz on a set
  containing `Ŷ₁, Y₁`: `f(Y₁) ≤ f(Y₀) + Lip · ϑ`);
  `IsRankAdaptiveBUGStep.energy_le_of_lipschitz_grad` (the paper's claim
  "`α = ‖Ûᵀ G(Y₀) V̂‖ + O(h)`, `β = ‖G(Y₁)‖ + O(ϑ)`" for a Lipschitz gradient, with explicit
  `O`-terms); `rankAdaptiveBUG_energy_le_sum` over many steps.
* `IsRankAdaptiveBUGStep.schrodinger_energy_untruncated_eq`,
  `IsRankAdaptiveBUGStep.schrodinger_energy_sub_le` (**Theorem 6**): for `F(Y) = -i H[Y]` with
  `H` self-adjoint, `E(Ŷ₁) = E(Y₀)` and `|E(Y₁) - E(Y₀)| ≤ γ ϑ`, `γ = ‖H[Y₁] + H[Ŷ₁]‖`.
* `IsRankAdaptiveBUGStep.hamiltonian_energy_untruncated_eq`,
  `IsRankAdaptiveBUGStep.hamiltonian_energy_sub_le`,
  `IsRankAdaptiveBUGStep.hamiltonian_energy_sub_le_of_lipschitz_grad` (**Theorem 7**): for
  `F = J ∇ℋ` with `J` skew and commuting with the projectors, `ℋ(Ŷ₁) = ℋ(Y₀)` and
  `|ℋ(Y₁) - ℋ(Y₀)| ≤ β ϑ`, `β = sup ‖∇ℋ‖` on `[Ŷ₁, Y₁]` `≤ ‖∇ℋ(Y₁)‖ + Lip(∇ℋ) ϑ`.

`IsAugmentedGalerkinStep` abstracts the S-step plus truncation for an arbitrary Galerkin
projector `R ∋ Y₀`; its Theorems 4, 5, 7 cover the rank-adaptive **Tucker** integrator of §4
(`R = ∏ᵢ P̂ᵢ`, `list_prod_apply_eq_self`), as claimed in §4.2.  `rotStep` is a non-trivial
conservative step (`ℂ` as a real space, `F(z) = -i z`) to which Theorems 4, 6 and 7 apply;
`constStep` is a gradient-system step (`F = -∇ℰ`, `ℰ(y) = -y` on `ℝ`) for which the bound of
Theorem 5 is attained.

**Theorem 1** (exactness) is `Exactness.augBug_exact_abstract` (abstract form) and
`Exactness.augBug_exact`, `Exactness.augBug_exact_ode` (matrix forms) in
`Integrators/Exactness.lean`; **Theorem 3** (preservation of (skew-)symmetry, before truncation)
is `Symmetry.augBug_isTwistSymm` in `Integrators/Matrix/Symmetry.lean`.

## Real formulation of Theorems 6 and 7

The complex matrix space `ℂ^{m×n}` is a real inner product space with `⟪Y, Z⟫_ℝ = Re⟨Y, Z⟩`,
whose norm is the complex Frobenius norm.  Multiplication by `-i` is a real-linear map `J` with
`⟪J Z, Z⟫_ℝ = 0`, and the complex projectors `Z ↦ Û Û* Z` and `Z ↦ Z V̂ V̂*` are complex linear,
i.e. commute with `J`.  For a complex-linear self-adjoint `H` the energy `⟨Y, H[Y]⟩` is real and
equals `⟪Y, H Y⟫_ℝ`, and the Schrödinger equation `i Ẏ = H[Y]` is `Ẏ = J H Y` (Theorem 6).  For
the Hamiltonian system (14) written as `i Ż = ∇_{Z̄} E` with `Z = Q + i P` (eq. (15)), in the real
coordinates `(Q, P)` the right-hand side is `J ∇H` with `J (a, b) = (b, -a)` skew, which is
`(-i)` times the identification, and the complex projectors commute with it (Theorem 7).  This
is exactly the abstract hypothesis `(J skew, J P₁ = P₁ J, J Q₁ = Q₁ J, F = J ∇ℋ)`.

## Deviations and generalizations

* Arbitrary real inner product space, abstract projectors; the K/L capture conditions are the
  ones of `IsBUGStep`; the augmentation enters only through `P₁ Y₀ = Y₀`, `Q₁ Y₀ = Y₀`.
* The truncation is any `Y₁` with `‖Y₁ - Ŷ₁‖ ≤ ϑ`; where the SVD structure matters (exact norm
  budget) we assume `Y₁ = T Ŷ₁` for an orthogonal projector `T` (for the truncated SVD,
  `T Z = U₁ U₁ᵀ Z V₁ V₁ᵀ`).
* Theorem 2: the paper states the bound with unspecified constants; ours are explicit, and the
  local error estimate is the one of `bug_local_error` plus `ϑ`.  The normal-component
  assumption is used only at the points `YK t₁`, `YL t₁` (as in `IsBUGStep`).
* Theorem 4 is proved in the two-sided form `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`, with the hypothesis
  `⟪F(t, Y), Y⟫ = 0` only needed on the Galerkin space; Theorems 6–7 likewise in two-sided form.
* Theorem 5: `α` and `β` are hypotheses (as in the paper's proof); for Lipschitz gradients we
  give the explicit `α = max(0, ‖P₁ Q₁ ∇f(Y₀)‖ - Lip(∇f) B h)` and `β = ‖∇f(Y₁)‖ + Lip(∇f) ϑ`.
* The exact flows `Φ n` from the numerical values (Lady Windermere's fan) are hypotheses; their
  existence is proved in `Foundations/Existence.lean`.
* Inexact substeps: the paper only remarks (after Theorem 2, citing Kieri–Lubich–Walach §2.6.3)
  that inexact substeps add an error bounded by their local errors; we prove it with explicit
  constants, keeping the normal-component assumption at the exact K- and L-step values
  `YK t₁`, `YL t₁` as in `IsBUGStep` (`ProjectorSplitting.lean` uses the computed values instead).
-/

open Set
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The rank-adaptive step -/

/-- All hypotheses of one step of the rank-adaptive (augmented) BUG integrator of
Ceruti–Kusch–Lubich ([CerutiKuschLubich2022, §2.1]) from `(t₀, Y₀)` to `t₁`: a BUG step
(`IsBUGStep`) with the old projectors `P₀, Q₀` (bases `U₀`, `V₀`) and the **augmented**
projectors `P₁, Q₁` (bases `Û`, `V̂` spanning `(K(t₁), U₀)` and `(L(t₁), V₀)`), such that the
augmented bases capture `Y₀`, followed by a truncation `Y₁` of the Galerkin result
`Ŷ₁ = YS t₁` to the tolerance `ϑ`. -/
structure IsRankAdaptiveBUGStep (F : ℝ → E → E) (ε ϑ : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK YL YS : ℝ → E) (Y₁ : E) : Prop
    extends IsBUGStep F ε P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS where
  /-- The augmented left basis `Û` captures `Y₀` (it spans `U₀`). -/
  augP : P₁ Y₀ = Y₀
  /-- The augmented right basis `V̂` captures `Y₀` (it spans `V₀`). -/
  augQ : Q₁ Y₀ = Y₀
  /-- Truncation to the tolerance `ϑ`: `‖Y₁ - Ŷ₁‖ ≤ ϑ`. -/
  trunc : ‖Y₁ - YS t₁‖ ≤ ϑ

/-- **Augmentation captures the starting value.**  If the augmented projector contains the old
one (`P₁ P₀ = P₀`, i.e. `Û Ûᵀ U₀ = U₀`) and `Y₀ = P₀ Y₀` (`Y₀ = U₀ S₀ V₀ᵀ`), then
`P₁ Y₀ = Y₀`. -/
lemma aug_fix_of_comp_eq {P₀ P₁ : E →L[ℝ] E} {Y₀ : E} (h : ∀ x, P₁ (P₀ x) = P₀ x)
    (hY : P₀ Y₀ = Y₀) : P₁ Y₀ = Y₀ := by
  rw [← hY, h]

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {ε ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E}

/-- The Galerkin projector `P₁ Q₁` (`Z ↦ Û Ûᵀ Z V̂ V̂ᵀ`) is an orthogonal projector. -/
lemma galerkinProj (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    IsOrthProj (P₁ * Q₁) :=
  hs.projP₁.mul hs.projQ₁ hs.comm₁

/-- The starting value lies in the Galerkin space: `Û Ûᵀ Y₀ V̂ V̂ᵀ = Y₀`. -/
lemma galerkin_fix (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    P₁ (Q₁ Y₀) = Y₀ := by
  rw [hs.augQ, hs.augP]

/-- **Lemma 1 of [CerutiKuschLubich2022]**: the Galerkin step of the rank-adaptive integrator starts
at `Ŷ₀ = Û Ŝ(t₀) V̂ᵀ = Y₀` (in contrast to the BUG integrator, where `Ŷ₀ = P₁ Q₁ Y₀ ≠ Y₀` in
general). -/
theorem start_eq (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    YS t₀ = Y₀ :=
  hs.sStart.trans hs.galerkin_fix

/-- The S-step as a Galerkin ODE for the projector `P₁ * Q₁`. -/
lemma sSol' (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    ODESolution (fun t x => (P₁ * Q₁) (F t x)) YS t₀ t₁ :=
  hs.sSol

/-- The S-step starts in the Galerkin space. -/
lemma start_mem (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    (P₁ * Q₁) (YS t₀) = YS t₀ := by
  rw [hs.start_eq]
  exact hs.galerkin_fix

/-- The S-step stays in the Galerkin space `{Û S V̂ᵀ}`. -/
theorem mem_range (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    ∀ t ∈ Icc t₀ t₁, P₁ (Q₁ (YS t)) = YS t :=
  hs.sSol'.galerkin_mem_range hs.galerkinProj hs.start_mem

/-- The truncation tolerance is nonnegative. -/
lemma tol_nonneg (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    0 ≤ ϑ :=
  (norm_nonneg _).trans hs.trunc

/-! ### Local error (Theorem 2) -/

section LocalError

variable {L B h : ℝ} {A : ℝ → E}

/-- **Robust local error of the untruncated rank-adaptive step** ([CerutiKuschLubich2022], proof of
Theorem 2, following Ceruti–Lubich Lemma 4): `‖Ŷ₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + 2ϑ_K) + 2ϑ_K`,
`ϑ_K = h (4 L B h + ε)`.  This is `bug_local_error` for the augmented projectors. -/
theorem local_error_untruncated
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖YS t₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) :=
  hs.toIsBUGStep.local_error hF hL hB ht₁ hh hA hA₀

/-- **Robust local error of the rank-adaptive integrator** ([CerutiKuschLubich2022, Thm. 2], local
form with explicit constants): the BUG local bound plus the truncation tolerance,
`‖Y₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + 2ϑ_K) + 2ϑ_K + ϑ`, `ϑ_K = h (4 L B h + ε)`. -/
theorem local_error (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
      + 2 * (h * (4 * L * B * h + ε)) + ϑ := by
  have h1 := hs.local_error_untruncated hF hL hB ht₁ hh hA hA₀
  have h2 := hs.trunc
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **Robust local error of the rank-adaptive integrator, `O`-form** ([CerutiKuschLubich2022],
Theorem 2): for `0 ≤ h ≤ H`, `‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h) + ϑ` with `c₁ = bugC₁ L H`,
`c₂ = bugC₂ L B H` independent of singular values. -/
theorem local_error_le (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := by
  have h1 := hs.toIsBUGStep.local_error_le hF hL hB ht₁ hh hhH hA hA₀
  have h2 := hs.trunc
  calc ‖Y₁ - A t₁‖ ≤ ‖Y₁ - YS t₁‖ + ‖YS t₁ - A t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end LocalError

end IsRankAdaptiveBUGStep

/-! ### Global error (Theorem 2) -/

section Global

variable {F : ℝ → E → E} {L B ε ϑ : ℝ}

/-- **Robust global error bound of the rank-adaptive integrator** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022, Thm. 2], with explicit constants).  Let `F` be `L`-Lipschitz (`L ≥ 0`) and
bounded by `B`, `tₙ = t₀ + n h` with `0 ≤ h ≤ H`, and `A` a solution of `A' = F(t, A)` on
`[t₀, t₀ + N h]`.  For `n < N` let step `n` go from `(tₙ, Y n)` to `Y (n+1)` as described by
`IsRankAdaptiveBUGStep` (old projectors `P n, Q n`, augmented projectors `Pa n, Qa n`,
truncation tolerance `ϑ`), and let `Φ n` be the exact flow on `[tₙ, tₙ₊₁]` started at `Y n`.
Then for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n (h (c₁ ε + c₂ h) + ϑ)),

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`. -/
theorem rankAdaptiveBUG_global_error (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε ϑ (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * (h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + ϑ := fun n hn =>
    (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  exact lady_windermere hF hL hh hA hΦ hΦ₀ hloc

/-- **Robust global error bound of the rank-adaptive integrator, final form**
(Ceruti–Kusch–Lubich, [CerutiKuschLubich2022, Thm. 2]): under the hypotheses of
`rankAdaptiveBUG_global_error`, with `‖Y 0 - A t₀‖ ≤ δ`, `ε ≥ 0` and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ n ϑ,

with `c₀ = c₃ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L H`, `c₂ = T e^{L T} bugC₂ L B H`, depending
only on `L`, `B`, `T` and the step-size bound `H` — in particular not on singular values. -/
theorem rankAdaptiveBUG_global_error_le (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hε : 0 ≤ ε) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ}
    {A : ℝ → E} (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E}
    {Y : ℕ → E} {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε ϑ (P n) (Q n) (Pa n) (Qa n) (t₀ + n * h)
      (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * n * ϑ := by
  intro n hn hT
  set g := bugC₁ L H * ε + bugC₂ L B H * h with hg_def
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ g :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  have h1 := rankAdaptiveBUG_global_error hF hL hB hh hhH hA hstep hΦ hΦ₀ n hn
  set X := ‖Y 0 - A t₀‖ + n * (h * g + ϑ) with hX_def
  have he := Real.exp_pos (L * (n * h))
  have hX : 0 ≤ X := by
    by_contra hcon
    have : Real.exp (L * (n * h)) * X < 0 := mul_neg_of_pos_of_neg he (lt_of_not_ge hcon)
    linarith [norm_nonneg (Y n - A (t₀ + n * h))]
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hXle : X ≤ δ + T * g + n * ϑ := by
    have : (n : ℝ) * h * g ≤ T * g := mul_le_mul_of_nonneg_right hT hg
    rw [hX_def]
    nlinarith
  calc ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * X := h1
    _ ≤ Real.exp (L * T) * X := mul_le_mul_of_nonneg_right hexp hX
    _ ≤ Real.exp (L * T) * (δ + T * g + n * ϑ) :=
        mul_le_mul_of_nonneg_left hXle (Real.exp_pos _).le
    _ = _ := by rw [hg_def]; ring

end Global

/-! ### Inexact substeps ([CerutiKuschLubich2022], remark after Theorem 2) -/

section InexactCapture

variable {F : ℝ → E → E} {L B ε : ℝ} {P₁ Q₀ : E →L[ℝ] E} {t₀ t₁ h : ℝ} {A YK : ℝ → E}

/-- **K-step capture lemma with an inexact K-step** ([CerutiKuschLubich2022], remark after Theorem
2; cf. Kieri–Lubich–Walach 2016, §2.6.3). As `kstep_capture`, but the new basis only captures a
computed approximation `K₁` of `YK t₁` (`P₁ K₁ = K₁`, `‖YK t₁ - K₁‖ ≤ η`): then
`‖(1 - P₁) (A t₁)‖ ≤ h (4 L B h + ε) + η`. -/
theorem kstep_capture_approx (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) (hP₁ : IsOrthProj P₁) (hQ₀ : IsOrthProj Q₀) (ht₁ : t₁ = t₀ + h)
    (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁)
    (hK : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁) (hK₀ : YK t₀ = A t₀) {K₁ : E}
    {η : ℝ} (hKcap : P₁ K₁ = K₁) (hη : ‖YK t₁ - K₁‖ ≤ η)
    (hε : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε) :
    ‖(1 - P₁) (A t₁)‖ ≤ h * (4 * L * B * h + ε) + η := by
  have hle : t₀ ≤ t₁ := by linarith
  set g : ℝ → E := fun t => (1 - P₁) (A t - YK t) with hg
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    (1 - P₁).continuous.comp_continuousOn (hA.cont.sub hK.cont)
  have hgd : ∀ t ∈ Ico t₀ t₁, HasDerivWithinAt g ((1 - P₁) (F t (A t) - Q₀ (F t (YK t))))
      (Ici t) t := fun t ht =>
    (1 - P₁).hasFDerivAt.comp_hasDerivWithinAt t ((hA.deriv t ht).sub (hK.deriv t ht))
  have hbound : ∀ t ∈ Ico t₀ t₁, ‖(1 - P₁) (F t (A t) - Q₀ (F t (YK t)))‖
      ≤ 4 * L * B * h + ε := fun t ht =>
    kstep_deriv_bound hF hL hB hP₁ hQ₀ ht₁ hA hK hK₀ (Ico_subset_Icc_self ht)
      (hε t (Ico_subset_Icc_self ht))
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd hbound t₁ ⟨hle, le_rfl⟩
  have hg₀ : g t₀ = 0 := by simp [hg, hK₀]
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rw [hg₀, sub_zero, hlen] at hmvt
  have hYK : ‖(1 - P₁) (YK t₁)‖ ≤ η := by
    have h1 := hP₁.norm_sub_le_of_mem_range (YK t₁) K₁ hKcap
    simpa using h1.trans hη
  have hdec : (1 - P₁) (A t₁) = g t₁ + (1 - P₁) (YK t₁) := by
    simp only [hg, map_sub]; abel
  rw [hdec]
  calc ‖g t₁ + (1 - P₁) (YK t₁)‖ ≤ ‖g t₁‖ + ‖(1 - P₁) (YK t₁)‖ := norm_add_le _ _
    _ ≤ (4 * L * B * h + ε) * h + η := add_le_add hmvt hYK
    _ = h * (4 * L * B * h + ε) + η := by ring

end InexactCapture

/-- One step of the rank-adaptive BUG integrator with **inexactly solved substeps**
([CerutiKuschLubich2022], remark after Theorem 2).  `YK`, `YL`, `YS` are the exact solutions of the
K-, L- and S-step differential equations; the computed K- and L-step results `K₁`, `L₁` and the
computed S-step result `Ŷ₁` have local errors at most `η`; the augmented bases span the
*computed* `K₁`, `L₁` and the old bases (so they capture `Y₀`); `Y₁` is the truncation of `Ŷ₁`
to the tolerance `ϑ`.  With `η = 0` this is `IsRankAdaptiveBUGStep`
(`IsRankAdaptiveBUGStep.toInexact`). -/
structure IsInexactRankAdaptiveBUGStep (F : ℝ → E → E) (ε η ϑ : ℝ) (P₀ Q₀ P₁ Q₁ : E →L[ℝ] E)
    (t₀ t₁ : ℝ) (Y₀ : E) (YK YL YS : ℝ → E) (K₁ L₁ Ŷ₁ Y₁ : E) : Prop where
  projP₀ : IsOrthProj P₀
  projQ₀ : IsOrthProj Q₀
  projP₁ : IsOrthProj P₁
  projQ₁ : IsOrthProj Q₁
  /-- The augmented left and right projectors commute. -/
  comm₁ : ∀ x, P₁ (Q₁ x) = Q₁ (P₁ x)
  /-- Exact K-step trajectory `YK' = Q₀ F(t, YK)`. -/
  kSol : ODESolution (fun t x => Q₀ (F t x)) YK t₀ t₁
  kStart : YK t₀ = Y₀
  /-- Local error of the computed K-step result. -/
  kApprox : ‖YK t₁ - K₁‖ ≤ η
  /-- The augmented left basis spans the computed `K₁`. -/
  kCap : P₁ K₁ = K₁
  kNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - P₁) ((1 - Q₀) (F t (YK t₁)))‖ ≤ ε
  /-- Exact L-step trajectory `YL' = P₀ F(t, YL)`. -/
  lSol : ODESolution (fun t x => P₀ (F t x)) YL t₀ t₁
  lStart : YL t₀ = Y₀
  /-- Local error of the computed L-step result. -/
  lApprox : ‖YL t₁ - L₁‖ ≤ η
  /-- The augmented right basis spans the computed `L₁`. -/
  lCap : Q₁ L₁ = L₁
  lNormal : ∀ t ∈ Icc t₀ t₁, ‖(1 - Q₁) ((1 - P₀) (F t (YL t₁)))‖ ≤ ε
  /-- The augmented left basis captures `Y₀`. -/
  augP : P₁ Y₀ = Y₀
  /-- The augmented right basis captures `Y₀`. -/
  augQ : Q₁ Y₀ = Y₀
  /-- Exact Galerkin S-step trajectory `YS' = P₁ Q₁ F(t, YS)`, `YS t₀ = P₁ Q₁ Y₀`. -/
  sSol : ODESolution (fun t x => P₁ (Q₁ (F t x))) YS t₀ t₁
  sStart : YS t₀ = P₁ (Q₁ Y₀)
  /-- Local error of the computed S-step result `Ŷ₁`. -/
  sApprox : ‖Ŷ₁ - YS t₁‖ ≤ η
  /-- Truncation to the tolerance `ϑ`. -/
  trunc : ‖Y₁ - Ŷ₁‖ ≤ ϑ

/-- An exact rank-adaptive step is an inexact one with `η = 0`. -/
theorem IsRankAdaptiveBUGStep.toInexact {F : ℝ → E → E} {ε ϑ : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} {Y₁ : E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    IsInexactRankAdaptiveBUGStep F ε 0 ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS (YK t₁) (YL t₁) (YS t₁)
      Y₁ where
  projP₀ := hs.projP₀
  projQ₀ := hs.projQ₀
  projP₁ := hs.projP₁
  projQ₁ := hs.projQ₁
  comm₁ := hs.comm₁
  kSol := hs.kSol
  kStart := hs.kStart
  kApprox := by simp
  kCap := hs.kCap
  kNormal := hs.kNormal
  lSol := hs.lSol
  lStart := hs.lStart
  lApprox := by simp
  lCap := hs.lCap
  lNormal := hs.lNormal
  augP := hs.augP
  augQ := hs.augQ
  sSol := hs.sSol
  sStart := hs.sStart
  sApprox := by simp
  trunc := hs.trunc

namespace IsInexactRankAdaptiveBUGStep

variable {F : ℝ → E → E} {ε η ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {K₁ L₁ Ŷ₁ Y₁ : E} {L B h : ℝ} {A : ℝ → E}

/-- The substep tolerance is nonnegative. -/
lemma eta_nonneg (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁ L₁
    Ŷ₁ Y₁) : 0 ≤ η :=
  (norm_nonneg _).trans hs.kApprox

/-- The Galerkin S-step of the inexact step still starts at `Y₀` (Lemma 1). -/
theorem start_eq (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁ L₁
    Ŷ₁ Y₁) : YS t₀ = Y₀ := by
  rw [hs.sStart, hs.augQ, hs.augP]

/-- **Capture with inexact K- and L-steps**: `‖A t₁ - P₁ Q₁ A t₁‖ ≤ 2 (ϑ_K + η)`,
`ϑ_K = h (4 L B h + ε)`. -/
theorem capture (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁ L₁
    Ŷ₁ Y₁) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖A t₁ - P₁ (Q₁ (A t₁))‖ ≤ 2 * (h * (4 * L * B * h + ε) + η) := by
  have h1 := kstep_capture_approx hF hL hB hs.projP₁ hs.projQ₀ ht₁ hh hA hs.kSol
    (hs.kStart.trans hA₀.symm) hs.kCap hs.kApprox hs.kNormal
  have h2 := kstep_capture_approx hF hL hB hs.projQ₁ hs.projP₀ ht₁ hh hA hs.lSol
    (hs.lStart.trans hA₀.symm) hs.lCap hs.lApprox hs.lNormal
  have h3 := norm_sub_apply_apply_le (Q := Q₁) hs.projP₁ (A t₁)
  linarith

/-- **Local error with inexact substeps** ([CerutiKuschLubich2022], remark after Theorem 2, explicit
form): with `ϑ_K = h (4 L B h + ε)` and `θ = 2 (ϑ_K + η)`,
`‖Y₁ - A t₁‖ ≤ (e^{L h} - 1)(B h + θ) + θ + η + ϑ`. -/
theorem local_error (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS K₁
    L₁ Ŷ₁ Y₁) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hA : ODESolution F A t₀ t₁) (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε) + η))
      + 2 * (h * (4 * L * B * h + ε) + η) + η + ϑ := by
  have hS := galerkin_step_error (R := P₁ * Q₁) (hs.projP₁.mul hs.projQ₁ hs.comm₁) hF hL hB ht₁
    hh hA hs.sSol (by rw [hs.sStart, hA₀]; rfl) (hs.capture hF hL hB ht₁ hh hA hA₀)
  have h1 := norm_sub_le_norm_sub_add_norm_sub Y₁ Ŷ₁ (A t₁)
  have h2 := norm_sub_le_norm_sub_add_norm_sub Ŷ₁ (YS t₁) (A t₁)
  linarith [hs.trunc, hs.sApprox]

/-- **Local error with inexact substeps, `O`-form** ([CerutiKuschLubich2022], remark after Theorem
2): for `0 ≤ h ≤ H`, `‖Y₁ - A t₁‖ ≤ h (c₁ ε + c₂ h) + (2 e^{L H} + 1) η + ϑ` with the constants
`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H` of the exact case: the substep errors enter additively, with
constants independent of singular values. -/
theorem local_error_le (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS
    K₁ L₁ Ŷ₁ Y₁) (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B)
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) {H : ℝ} (hhH : h ≤ H) (hA : ODESolution F A t₀ t₁)
    (hA₀ : A t₀ = Y₀) :
    ‖Y₁ - A t₁‖ ≤ h * (bugC₁ L H * ε + bugC₂ L B H * h)
      + (2 * Real.exp (L * H) + 1) * η + ϑ := by
  have h0 := hs.local_error hF hL hB ht₁ hh hA hA₀
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hs.kNormal t₀ ⟨le_rfl, by linarith⟩)
  have hb := bug_bound_le hL hB.nonneg hε hh hhH
  have hη := hs.eta_nonneg
  have hexp : Real.exp (L * h) ≤ Real.exp (L * H) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hhH hL)
  have hsplit : (Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε) + η))
      + 2 * (h * (4 * L * B * h + ε) + η) + η + ϑ
      = ((Real.exp (L * h) - 1) * (B * h + 2 * (h * (4 * L * B * h + ε)))
        + 2 * (h * (4 * L * B * h + ε))) + (2 * Real.exp (L * h) + 1) * η + ϑ := by ring
  have h3 : (2 * Real.exp (L * h) + 1) * η ≤ (2 * Real.exp (L * H) + 1) * η :=
    mul_le_mul_of_nonneg_right (by linarith) hη
  linarith

/-- **Norm conservation with inexact S-step** ([CerutiKuschLubich2022, Thm. 4] with the remark after
Theorem 2): if `⟪F(t, Y), Y⟫ = 0` on the Galerkin space, then `|‖Y₁‖ - ‖Y₀‖| ≤ η + ϑ`. -/
theorem abs_norm_sub_le (hs : IsInexactRankAdaptiveBUGStep F ε η ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS
    K₁ L₁ Ŷ₁ Y₁) (h01 : t₀ ≤ t₁) (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) :
    |‖Y₁‖ - ‖Y₀‖| ≤ η + ϑ := by
  have hR := hs.projP₁.mul hs.projQ₁ hs.comm₁
  have h0 : (P₁ * Q₁) (YS t₀) = YS t₀ := by
    rw [hs.start_eq]; change P₁ (Q₁ Y₀) = Y₀; rw [hs.augQ, hs.augP]
  have h := hs.sSol.galerkin_norm_eq' hR h0 hF t₁ ⟨h01, le_rfl⟩
  rw [hs.start_eq] at h
  rw [← h]
  calc |‖Y₁‖ - ‖YS t₁‖| ≤ ‖Y₁ - YS t₁‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖Y₁ - Ŷ₁‖ + ‖Ŷ₁ - YS t₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η + ϑ := by linarith [hs.trunc, hs.sApprox]

end IsInexactRankAdaptiveBUGStep

/-- **Robust global error with inexact substeps** (Ceruti–Kusch–Lubich, [CerutiKuschLubich2022],
Theorem 2 and the remark following it, explicit constants): under the hypotheses of
`rankAdaptiveBUG_global_error`, but with substeps solved up to local errors `η`
(`IsInexactRankAdaptiveBUGStep`), for `n ≤ N`

    ‖Y n - A tₙ‖ ≤ e^{L n h} (‖Y 0 - A t₀‖ + n (h (c₁ ε + c₂ h) + (2 e^{L H} + 1) η + ϑ)),

`c₁ = bugC₁ L H`, `c₂ = bugC₂ L B H`: the additional error is bounded in terms of the local
errors of the inexact substeps, with constants independent of singular values. -/
theorem rankAdaptiveBUG_inexact_global_error {F : ℝ → E → E} {L B ε η ϑ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (hB : IsBoundedField F B) {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y K L' Ŷ : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsInexactRankAdaptiveBUGStep F ε η ϑ (P n) (Q n) (Pa n) (Qa n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (K n) (L' n) (Ŷ n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) :
    ∀ n ≤ N, ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) *
      (‖Y 0 - A t₀‖ + n * (h * (bugC₁ L H * ε + bugC₂ L B H * h)
        + (2 * Real.exp (L * H) + 1) * η + ϑ)) := by
  have hloc : ∀ n < N, ‖Y (n + 1) - Φ n (t₀ + (n + 1) * h)‖ ≤
      h * (bugC₁ L H * ε + bugC₂ L B H * h) + (2 * Real.exp (L * H) + 1) * η + ϑ :=
    fun n hn => (hstep n hn).local_error_le hF hL hB (by ring) hh hhH (hΦ n hn) (hΦ₀ n hn)
  exact lady_windermere hF hL hh hA hΦ hΦ₀ hloc

/-- **Robust global error with inexact substeps, final form** ([CerutiKuschLubich2022, Thm. 2] and
the remark following it): under the hypotheses of `rankAdaptiveBUG_inexact_global_error`, with
`‖Y 0 - A t₀‖ ≤ δ`, `ε ≥ 0` and `n h ≤ T`,

    ‖Y n - A tₙ‖ ≤ c₀ δ + c₁ ε + c₂ h + c₃ n (ϑ + c₄ η),

with `c₀ = c₃ = e^{L T}`, `c₁ = T e^{L T} bugC₁ L H`, `c₂ = T e^{L T} bugC₂ L B H` as in
`rankAdaptiveBUG_global_error_le` and `c₄ = 2 e^{L H} + 1`. -/
theorem rankAdaptiveBUG_inexact_global_error_le {F : ℝ → E → E} {L B ε η ϑ : ℝ}
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (hB : IsBoundedField F B) (hε : 0 ≤ ε)
    {t₀ h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) {N : ℕ} {A : ℝ → E}
    (hA : ODESolution F A t₀ (t₀ + N * h)) {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y K L' Ŷ : ℕ → E}
    {YK YL YS Φ : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsInexactRankAdaptiveBUGStep F ε η ϑ (P n) (Q n) (Pa n) (Qa n)
      (t₀ + n * h) (t₀ + (n + 1) * h) (Y n) (YK n) (YL n) (YS n) (K n) (L' n) (Ŷ n) (Y (n + 1)))
    (hΦ : ∀ n < N, ODESolution F (Φ n) (t₀ + n * h) (t₀ + (n + 1) * h))
    (hΦ₀ : ∀ n < N, Φ n (t₀ + n * h) = Y n) {δ T : ℝ} (hδ : ‖Y 0 - A t₀‖ ≤ δ) :
    ∀ n ≤ N, (n : ℝ) * h ≤ T →
      ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * T) * δ
        + T * Real.exp (L * T) * bugC₁ L H * ε + T * Real.exp (L * T) * bugC₂ L B H * h
        + Real.exp (L * T) * n * (ϑ + (2 * Real.exp (L * H) + 1) * η) := by
  intro n hn hT
  set g := bugC₁ L H * ε + bugC₂ L B H * h with hg_def
  set ϑ' := ϑ + (2 * Real.exp (L * H) + 1) * η with hϑ'
  have hH : 0 ≤ H := hh.trans hhH
  have hg : 0 ≤ g :=
    add_nonneg (mul_nonneg (bugC₁_nonneg hL hH) hε)
      (mul_nonneg (bugC₂_nonneg hL hB.nonneg hH) hh)
  have h1 := rankAdaptiveBUG_inexact_global_error hF hL hB hh hhH hA hstep hΦ hΦ₀ n hn
  have hX_eq : ‖Y 0 - A t₀‖ + n * (h * g + (2 * Real.exp (L * H) + 1) * η + ϑ)
      = ‖Y 0 - A t₀‖ + n * (h * g + ϑ') := by rw [hϑ']; ring
  rw [hX_eq] at h1
  set X := ‖Y 0 - A t₀‖ + n * (h * g + ϑ') with hX_def
  have he := Real.exp_pos (L * (n * h))
  have hX : 0 ≤ X := by
    by_contra hcon
    have : Real.exp (L * (n * h)) * X < 0 := mul_neg_of_pos_of_neg he (lt_of_not_ge hcon)
    linarith [norm_nonneg (Y n - A (t₀ + n * h))]
  have hexp : Real.exp (L * (n * h)) ≤ Real.exp (L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hL)
  have hXle : X ≤ δ + T * g + n * ϑ' := by
    have : (n : ℝ) * h * g ≤ T * g := mul_le_mul_of_nonneg_right hT hg
    rw [hX_def]
    nlinarith
  calc ‖Y n - A (t₀ + n * h)‖ ≤ Real.exp (L * (n * h)) * X := h1
    _ ≤ Real.exp (L * T) * X := mul_le_mul_of_nonneg_right hexp hX
    _ ≤ Real.exp (L * T) * (δ + T * g + n * ϑ') :=
        mul_le_mul_of_nonneg_left hXle (Real.exp_pos _).le
    _ = _ := by rw [hg_def]; ring

/-! ### Norm conservation up to the truncation tolerance (Theorem 4) -/

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {ε ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E}

section Norm

/-- **Norm conservation of the untruncated step** ([CerutiKuschLubich2022], proof of Theorem 4): if
`⟪F(t, Y), Y⟫ = 0` for all `Y` in the Galerkin space (in particular under condition (12)), then
`‖Ŷ₁‖ = ‖Y₀‖`, independently of the step size.  This uses Lemma 1 (`start_eq`). -/
theorem norm_untruncated_eq (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ := by
  have h := hs.sSol'.galerkin_norm_eq' hs.galerkinProj hs.start_mem hF t₁ ⟨h01, le_rfl⟩
  rwa [hs.start_eq] at h

/-- **Norm conservation up to the truncation tolerance** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022, Thm. 4], two-sided form): if `⟪F(t, Y), Y⟫ = 0` on the Galerkin space, then
`|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`, independently of the step size. -/
theorem abs_norm_sub_le (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) : |‖Y₁‖ - ‖Y₀‖| ≤ ϑ := by
  rw [← hs.norm_untruncated_eq h01 hF]
  exact (abs_norm_sub_norm_le _ _).trans hs.trunc

/-- **Theorem 4 of [CerutiKuschLubich2022]** under the paper's condition (12),
`⟪Y, F(t, Y)⟫ = 0` for all `Y` and `t`: `‖Y₁‖ - ‖Y₀‖ ≤ ϑ` (in fact `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`). -/
theorem norm_sub_le (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hF : ∀ t Y, ⟪Y, F t Y⟫ = 0) : ‖Y₁‖ - ‖Y₀‖ ≤ ϑ :=
  (le_abs_self _).trans <| hs.abs_norm_sub_le h01 fun t x _ => by rw [real_inner_comm, hF]

/-- **Exact norm budget for a projection truncation.**  If the truncation is an orthogonal
projection of `Ŷ₁` (as the truncated SVD `Y₁ = U₁ U₁ᵀ Ŷ₁ V₁ V₁ᵀ` is) and the field is
conservative on the Galerkin space, then `‖Y₁‖² + ‖Y₁ - Ŷ₁‖² = ‖Y₀‖²`. -/
theorem norm_sq_add_of_proj
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) {T : E →L[ℝ] E} (hT : IsOrthProj T)
    (hY₁ : Y₁ = T (YS t₁)) : ‖Y₁‖ ^ 2 + ‖Y₁ - YS t₁‖ ^ 2 = ‖Y₀‖ ^ 2 := by
  rw [← hs.norm_untruncated_eq h01 hF, ← hT.norm_sq_add (YS t₁), hY₁, norm_sub_rev]

/-- **Norm bounds for a projection truncation**: under the hypotheses of
`norm_sq_add_of_proj`, `‖Y₀‖² - ϑ² ≤ ‖Y₁‖² ≤ ‖Y₀‖²`; in particular the norm never increases. -/
theorem norm_sq_bounds_of_proj
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ = 0) {T : E →L[ℝ] E} (hT : IsOrthProj T)
    (hY₁ : Y₁ = T (YS t₁)) : ‖Y₀‖ ^ 2 - ϑ ^ 2 ≤ ‖Y₁‖ ^ 2 ∧ ‖Y₁‖ ≤ ‖Y₀‖ := by
  have h := hs.norm_sq_add_of_proj h01 hF hT hY₁
  have ht : ‖Y₁ - YS t₁‖ ^ 2 ≤ ϑ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs.trunc 2
  refine ⟨by linarith, ?_⟩
  have h2 : 0 ≤ ‖Y₁ - YS t₁‖ ^ 2 := sq_nonneg _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- **Norm dissipation up to truncation**: if `⟪F(t, Y), Y⟫ ≤ 0` on the Galerkin space (e.g. a
dissipative linear field), then `‖Ŷ₁‖ ≤ ‖Y₀‖` and `‖Y₁‖ ≤ ‖Y₀‖ + ϑ`, for every step size. -/
theorem norm_le_of_dissipative
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, P₁ (Q₁ x) = x → ⟪F t x, x⟫ ≤ 0) : ‖YS t₁‖ ≤ ‖Y₀‖ ∧ ‖Y₁‖ ≤ ‖Y₀‖ + ϑ := by
  have h := hs.sSol'.galerkin_norm_le' hs.galerkinProj hs.start_mem hF t₁ ⟨h01, le_rfl⟩
  rw [hs.start_eq] at h
  refine ⟨h, ?_⟩
  have h2 := norm_le_norm_add_norm_sub' Y₁ (YS t₁)
  linarith [hs.trunc]

end Norm

end IsRankAdaptiveBUGStep

/-- **Norm drift over many steps** ([CerutiKuschLubich2022, Thm. 4] iterated): for a sequence of
rank-adaptive steps with arbitrary (nondecreasing) time grid `τ` and truncation tolerance `ϑ`,
if `⟪F(t, Y), Y⟫ = 0` for all `t, Y`, then `|‖Yₙ‖ - ‖Y₀‖| ≤ n ϑ` for `n ≤ N`, independently of
the step sizes. -/
theorem rankAdaptiveBUG_norm_drift {F : ℝ → E → E} {ε ϑ : ℝ} {τ : ℕ → ℝ} {N : ℕ}
    {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε ϑ (P n) (Q n) (Pa n) (Qa n) (τ n) (τ (n + 1))
      (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hF : ∀ t x, ⟪F t x, x⟫ = 0) :
    ∀ n ≤ N, |‖Y n‖ - ‖Y 0‖| ≤ n * ϑ := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < N := Nat.lt_of_succ_le hn
    have h1 := (hstep n hn').abs_norm_sub_le (hτ n hn') fun t x _ => hF t x
    have h2 := ih hn'.le
    calc |‖Y (n + 1)‖ - ‖Y 0‖| ≤ |‖Y (n + 1)‖ - ‖Y n‖| + |‖Y n‖ - ‖Y 0‖| :=
          abs_sub_le _ _ _
      _ ≤ ϑ + n * ϑ := add_le_add h1 h2
      _ = ((n + 1 : ℕ) : ℝ) * ϑ := by push_cast; ring

/-! ### Gradient systems (Theorem 5) -/

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {ε ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E} {ℰ : E → ℝ} {g : E → E}

section Gradient

/-- For a gradient system `F(t, Y) = -∇ℰ(Y)` the S-step is the projected gradient flow
`Ŷ' = -P₁ Q₁ ∇ℰ(Ŷ)`. -/
lemma sSol_gradFlow (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hFg : ∀ t x, F t x = -g x) : ODESolution (fun _ x => -(P₁ * Q₁) (g x)) YS t₀ t₁ := by
  have hfun : (fun t x => P₁ (Q₁ (F t x))) = fun _ x => -(P₁ * Q₁) (g x) := by
    funext t x
    rw [hFg, map_neg, map_neg]
    rfl
  exact hfun ▸ hs.sSol

/-- **Energy decrease of the untruncated step for gradient systems** ([CerutiKuschLubich2022], proof
of Theorem 5): if `F = -∇ℰ` and `α² ≤ ‖Û Ûᵀ ∇ℰ(Ŷ(t)) V̂ V̂ᵀ‖²` along the S-step, then
`ℰ(Ŷ₁) ≤ ℰ(Y₀) - α² (t₁ - t₀)`. (Uses Lemma 1: the S-step starts at `Y₀`.) -/
theorem energy_untruncated_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hFg : ∀ t x, F t x = -g x) {α : ℝ}
    (hα : ∀ t ∈ Ico t₀ t₁, α ^ 2 ≤ ‖P₁ (Q₁ (g (YS t)))‖ ^ 2) :
    ℰ (YS t₁) ≤ ℰ Y₀ - α ^ 2 * (t₁ - t₀) := by
  have h := (hs.sSol_gradFlow hFg).energy_le_sub_gradFlow hs.galerkinProj hℰ hα t₁
    ⟨h01, le_rfl⟩
  rwa [hs.start_eq] at h

/-- **Energy decrease up to truncation for gradient systems** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022], **Theorem 5**): for `F = -∇ℰ`, with `α² ≤ ‖Û Ûᵀ ∇ℰ(Ŷ(t)) V̂ V̂ᵀ‖²` along
the S-step and `‖∇ℰ‖ ≤ β` on the segment `[Ŷ₁, Y₁]`,

    ℰ(Y₁) ≤ ℰ(Y₀) - α² h + β ϑ,     h = t₁ - t₀. -/
theorem energy_le (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hFg : ∀ t x, F t x = -g x)
    {α : ℝ} (hα : ∀ t ∈ Ico t₀ t₁, α ^ 2 ≤ ‖P₁ (Q₁ (g (YS t)))‖ ^ 2) {β : ℝ}
    (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    ℰ Y₁ ≤ ℰ Y₀ - α ^ 2 * (t₁ - t₀) + β * ϑ := by
  have h := (hs.sSol_gradFlow hFg).truncated_energy_le_gradFlow hs.galerkinProj hℰ h01 hα
    hs.trunc hβ
  rwa [hs.start_eq] at h

/-- **Monotonicity up to truncation** (Theorem 5 with `α = 0`): for `F = -∇ℰ`,
`ℰ(Ŷ₁) ≤ ℰ(Y₀)` and `ℰ(Y₁) ≤ ℰ(Y₀) + β ϑ` if `‖∇ℰ‖ ≤ β` on `[Ŷ₁, Y₁]`. -/
theorem energy_le_add (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (h01 : t₀ ≤ t₁) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hFg : ∀ t x, F t x = -g x)
    {β : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    ℰ (YS t₁) ≤ ℰ Y₀ ∧ ℰ Y₁ ≤ ℰ Y₀ + β * ϑ := by
  have hα : ∀ t ∈ Ico t₀ t₁, (0 : ℝ) ^ 2 ≤ ‖P₁ (Q₁ (g (YS t)))‖ ^ 2 := fun t _ => by
    rw [zero_pow two_ne_zero]; positivity
  have h1 := hs.energy_untruncated_le h01 hℰ hFg hα
  have h2 := hs.energy_le h01 hℰ hFg hα hβ
  constructor <;> linarith

/-- **Theorem 5 for a Lipschitz energy** ([CerutiKuschLubich2022, Thm. 5], the form requested for
`ℰ` Lipschitz on the relevant set): if `ℰ` is `Λ`-Lipschitz on a set `s` containing `Ŷ₁` and
`Y₁`, then `ℰ(Y₁) ≤ ℰ(Y₀) + Λ ϑ`. -/
theorem energy_le_of_lipschitzOnWith
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hFg : ∀ t x, F t x = -g x) {Λ : NNReal}
    {s : Set E} (hLip : LipschitzOnWith Λ ℰ s) (h1 : YS t₁ ∈ s) (h2 : Y₁ ∈ s) :
    ℰ Y₁ ≤ ℰ Y₀ + Λ * ϑ := by
  have hα : ∀ t ∈ Ico t₀ t₁, (0 : ℝ) ^ 2 ≤ ‖P₁ (Q₁ (g (YS t)))‖ ^ 2 := fun t _ => by
    rw [zero_pow two_ne_zero]; positivity
  have h0 := hs.energy_untruncated_le h01 hℰ hFg hα
  have hd := hLip.dist_le_mul Y₁ h2 (YS t₁) h1
  rw [Real.dist_eq, dist_eq_norm] at hd
  have h3 : ℰ Y₁ - ℰ (YS t₁) ≤ Λ * ϑ :=
    (le_abs_self _).trans (hd.trans (mul_le_mul_of_nonneg_left hs.trunc Λ.2))
  linarith

/-- On the truncation segment `[Ŷ₁, Y₁]`, an `Lg`-Lipschitz map `g` is bounded by
`‖g(Y₁)‖ + Lg ϑ`. -/
lemma norm_le_on_segment (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    {Lg : ℝ} (hLg : 0 ≤ Lg) (hgL : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖) :
    ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ ‖g Y₁‖ + Lg * ϑ := by
  intro w hw
  have hw' : ‖w - Y₁‖ ≤ ϑ := by
    have h := segment_subset_closedBall_right (YS t₁) Y₁ hw
    rw [Metric.mem_closedBall, dist_eq_norm, dist_eq_norm, norm_sub_rev (YS t₁)] at h
    exact h.trans hs.trunc
  calc ‖g w‖ ≤ ‖g Y₁‖ + ‖g w - g Y₁‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖g Y₁‖ + Lg * ϑ :=
        add_le_add le_rfl ((hgL _ _).trans (mul_le_mul_of_nonneg_left hw' hLg))

/-- **Theorem 5 with explicit `α` and `β` for a Lipschitz gradient** ([CerutiKuschLubich2022],
Theorem 5, second sentence: "`α = ‖Ûᵀ G(Y₀) V̂‖ + O(h)` and `β = ‖G(Y₁)‖ + O(ϑ)`").  If
`G = ∇ℰ` is `Lg`-Lipschitz and bounded by `Bg`, `F = -G` and `t₁ = t₀ + h`, then

    ℰ(Y₁) ≤ ℰ(Y₀) - max(0, ‖Û Ûᵀ G(Y₀) V̂ V̂ᵀ‖ - Lg Bg h)² h + (‖G(Y₁)‖ + Lg ϑ) ϑ.

(`‖Û Ûᵀ X V̂ V̂ᵀ‖ = ‖Ûᵀ X V̂‖` for orthonormal `Û`, `V̂`.) -/
theorem energy_le_of_lipschitz_grad
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) {h : ℝ}
    (ht₁ : t₁ = t₀ + h) (hh : 0 ≤ h) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hFg : ∀ t x, F t x = -g x) {Lg Bg : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖) (hgB : ∀ x, ‖g x‖ ≤ Bg) :
    ℰ Y₁ ≤ ℰ Y₀ - max 0 (‖P₁ (Q₁ (g Y₀))‖ - Lg * Bg * h) ^ 2 * h
      + (‖g Y₁‖ + Lg * ϑ) * ϑ := by
  have h01 : t₀ ≤ t₁ := by linarith
  have hFB : IsBoundedField F Bg := fun t x => by rw [hFg, norm_neg]; exact hgB x
  have hspeed := hs.sSol'.norm_sub_start_le_of_proj hFB hs.galerkinProj ht₁
  have hα : ∀ t ∈ Ico t₀ t₁,
      max 0 (‖P₁ (Q₁ (g Y₀))‖ - Lg * Bg * h) ^ 2 ≤ ‖P₁ (Q₁ (g (YS t)))‖ ^ 2 := by
    intro t ht
    have hd : ‖YS t - Y₀‖ ≤ Bg * h := by
      have h' := hspeed t (Ico_subset_Icc_self ht)
      rwa [hs.start_eq] at h'
    have h1 : ‖P₁ (Q₁ (g Y₀))‖ - ‖P₁ (Q₁ (g (YS t)))‖ ≤ Lg * Bg * h := by
      calc ‖P₁ (Q₁ (g Y₀))‖ - ‖P₁ (Q₁ (g (YS t)))‖
          ≤ ‖P₁ (Q₁ (g Y₀)) - P₁ (Q₁ (g (YS t)))‖ := norm_sub_norm_le _ _
        _ = ‖(P₁ * Q₁) (g Y₀ - g (YS t))‖ := by rw [map_sub]; rfl
        _ ≤ ‖g Y₀ - g (YS t)‖ := hs.galerkinProj.norm_le _
        _ ≤ Lg * ‖Y₀ - YS t‖ := hgL _ _
        _ ≤ Lg * (Bg * h) := mul_le_mul_of_nonneg_left (by rwa [norm_sub_rev]) hLg
        _ = Lg * Bg * h := by ring
    have h2 : max 0 (‖P₁ (Q₁ (g Y₀))‖ - Lg * Bg * h) ≤ ‖P₁ (Q₁ (g (YS t)))‖ :=
      max_le (norm_nonneg _) (by linarith)
    exact pow_le_pow_left₀ (le_max_left _ _) h2 2
  have hE := hs.energy_le h01 hℰ hFg hα (hs.norm_le_on_segment hLg hgL)
  have hlen : t₁ - t₀ = h := by rw [ht₁]; ring
  rwa [hlen] at hE

end Gradient

/-! ### Energy conservation: Schrödinger and Hamiltonian systems (Theorems 6 and 7) -/

section Hamiltonian

/-- If `J` commutes with `P₁` and `Q₁`, it commutes with the Galerkin projector `P₁ Q₁`. -/
lemma comm_galerkinProj {J : E →L[ℝ] E} (hJP : ∀ z, J (P₁ z) = P₁ (J z))
    (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z)) (z : E) : J ((P₁ * Q₁) z) = (P₁ * Q₁) (J z) := by
  change J (P₁ (Q₁ z)) = P₁ (Q₁ (J z))
  rw [hJP, hJQ]

/-- **Energy conservation of the untruncated step** ([CerutiKuschLubich2022], proof of Theorem 7):
for `F = J ∇ℋ` with `J` skew (`⟪J z, z⟫ = 0`) and commuting with `P₁` and `Q₁` (in the complex
formulation: `J = -i` and complex-linear projectors), `ℋ(Ŷ₁) = ℋ(Y₀)`, for every step size. -/
theorem hamiltonian_energy_untruncated_eq
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJP : ∀ z, J (P₁ z) = P₁ (J z)) (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z))
    (hFJ : ∀ t x, F t x = J (g x)) : ℰ (YS t₁) = ℰ Y₀ := by
  have h := hs.sSol'.galerkin_energy_eq_of_skew hs.galerkinProj hℰ hJ
    (comm_galerkinProj hJP hJQ) hFJ t₁ ⟨h01, le_rfl⟩
  rwa [hs.start_eq] at h

/-- **Energy conservation up to truncation for Hamiltonian systems** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022], **Theorem 7**, real formulation): for `F = J ∇ℋ` with `J` skew and
commuting with `P₁`, `Q₁`, and `‖∇ℋ‖ ≤ β` on the segment `[Ŷ₁, Y₁]`, `|ℋ(Y₁) - ℋ(Y₀)| ≤ β ϑ`. -/
theorem hamiltonian_energy_sub_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJP : ∀ z, J (P₁ z) = P₁ (J z)) (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z))
    (hFJ : ∀ t x, F t x = J (g x)) {β : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    |ℰ Y₁ - ℰ Y₀| ≤ β * ϑ := by
  have h := hs.sSol'.truncated_energy_sub_le_of_skew hs.galerkinProj hℰ hJ
    (comm_galerkinProj hJP hJQ) hFJ h01 hs.trunc hβ
  rwa [hs.start_eq] at h

/-- **Theorem 7 of [CerutiKuschLubich2022] with explicit `β`**: if moreover `∇ℋ` is `Lg`-Lipschitz,
`|ℋ(Y₁) - ℋ(Y₀)| ≤ (‖∇ℋ(Y₁)‖ + Lg ϑ) ϑ`, i.e. `β = ‖∇ℋ(Y₁)‖ + O(ϑ)` as stated in the paper. -/
theorem hamiltonian_energy_sub_le_of_lipschitz_grad
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0)
    (hJP : ∀ z, J (P₁ z) = P₁ (J z)) (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z))
    (hFJ : ∀ t x, F t x = J (g x)) {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖) :
    |ℰ Y₁ - ℰ Y₀| ≤ (‖g Y₁‖ + Lg * ϑ) * ϑ :=
  hs.hamiltonian_energy_sub_le h01 hℰ hJ hJP hJQ hFJ (hs.norm_le_on_segment hLg hgL)

end Hamiltonian

end IsRankAdaptiveBUGStep

/-- For a symmetric `H`: `⟪x, H x⟫ - ⟪y, H y⟫ = ⟪x - y, H x + H y⟫`. -/
lemma inner_apply_self_sub_eq {H : E →L[ℝ] E} (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫) (x y : E) :
    ⟪x, H x⟫ - ⟪y, H y⟫ = ⟪x - y, H x + H y⟫ := by
  have h : ⟪x, H y⟫ = ⟪y, H x⟫ := by rw [← hH, real_inner_comm]
  rw [inner_sub_left, inner_add_right, inner_add_right, h]
  ring

/-- For a symmetric `H`, the quadratic energy `x ↦ ⟪x, H x⟫` has gradient `2 H x`. -/
lemma hasFDerivAt_inner_apply_self {H : E →L[ℝ] E} (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫) (x : E) :
    HasFDerivAt (fun x => ⟪x, H x⟫) (innerSL ℝ ((2 : ℝ) • H x)) x := by
  have h := (hasFDerivAt_id x).inner ℝ H.hasFDerivAt
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    id_eq, ContinuousLinearMap.coe_id', innerSL_apply_apply, real_inner_smul_left]
  rw [← hH x v, real_inner_comm v]
  ring

namespace IsRankAdaptiveBUGStep

variable {F : ℝ → E → E} {ε ϑ : ℝ} {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E}
  {YK YL YS : ℝ → E} {Y₁ : E}

section Schrodinger

/-- **Energy conservation of the untruncated step for Schrödinger equations**
([CerutiKuschLubich2022], proof of Theorem 6, real formulation): for `F(Y) = J H Y` (`J = -i`) with
`J` skew and commuting with `P₁`, `Q₁`, and `H` self-adjoint (`H` commuting with `J` is not
needed), the energy `E(Y) = ⟪Y, H Y⟫` satisfies `E(Ŷ₁) = E(Y₀)`. -/
theorem schrodinger_energy_untruncated_eq
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    {J H : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ z, J (P₁ z) = P₁ (J z))
    (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z)) (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hFJ : ∀ t x, F t x = J (H x)) : ⟪YS t₁, H (YS t₁)⟫ = ⟪Y₀, H Y₀⟫ := by
  refine hs.hamiltonian_energy_untruncated_eq (ℰ := fun x => ⟪x, H x⟫)
    (g := fun x => (2 : ℝ) • H x) (J := (2⁻¹ : ℝ) • J) h01 (hasFDerivAt_inner_apply_self hH)
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun t x => ?_)
  · rw [smul_apply, real_inner_smul_left, hJ, mul_zero]
  · rw [smul_apply, smul_apply, hJP, map_smul]
  · rw [smul_apply, smul_apply, hJQ, map_smul]
  · rw [hFJ, smul_apply, map_smul, smul_smul]
    norm_num

/-- **Energy conservation up to truncation for Schrödinger equations** (Ceruti–Kusch–Lubich,
[CerutiKuschLubich2022], **Theorem 6**, real formulation, two-sided): under the hypotheses of
`schrodinger_energy_untruncated_eq`,

    |E(Y₁) - E(Y₀)| ≤ γ ϑ,     γ = ‖H Y₁ + H Ŷ₁‖. -/
theorem schrodinger_energy_sub_le
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) (h01 : t₀ ≤ t₁)
    {J H : E →L[ℝ] E} (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJP : ∀ z, J (P₁ z) = P₁ (J z))
    (hJQ : ∀ z, J (Q₁ z) = Q₁ (J z)) (hH : ∀ x y, ⟪H x, y⟫ = ⟪x, H y⟫)
    (hFJ : ∀ t x, F t x = J (H x)) :
    |⟪Y₁, H Y₁⟫ - ⟪Y₀, H Y₀⟫| ≤ ‖H Y₁ + H (YS t₁)‖ * ϑ := by
  rw [← hs.schrodinger_energy_untruncated_eq h01 hJ hJP hJQ hH hFJ, inner_apply_self_sub_eq hH]
  calc |⟪Y₁ - YS t₁, H Y₁ + H (YS t₁)⟫| ≤ ‖Y₁ - YS t₁‖ * ‖H Y₁ + H (YS t₁)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ϑ * ‖H Y₁ + H (YS t₁)‖ := mul_le_mul_of_nonneg_right hs.trunc (norm_nonneg _)
    _ = ‖H Y₁ + H (YS t₁)‖ * ϑ := mul_comm _ _

end Schrodinger

end IsRankAdaptiveBUGStep

/-- **Energy over many steps for gradient systems** ([CerutiKuschLubich2022, Thm. 5] iterated with
`α = 0`): for a sequence of rank-adaptive steps on a nondecreasing time grid `τ` applied to
`F = -∇ℰ`, with `‖∇ℰ‖ ≤ β k` on the truncation segment of step `k`,
`ℰ(Yₙ) ≤ ℰ(Y₀) + (∑_{k < n} β k) ϑ`. -/
theorem rankAdaptiveBUG_energy_le_sum {F : ℝ → E → E} {ε ϑ : ℝ} {τ : ℕ → ℝ} {N : ℕ}
    {P Q Pa Qa : ℕ → E →L[ℝ] E} {Y : ℕ → E} {YK YL YS : ℕ → ℝ → E} {ℰ : E → ℝ} {g : E → E}
    (hstep : ∀ n < N, IsRankAdaptiveBUGStep F ε ϑ (P n) (Q n) (Pa n) (Qa n) (τ n) (τ (n + 1))
      (Y n) (YK n) (YL n) (YS n) (Y (n + 1)))
    (hτ : ∀ n < N, τ n ≤ τ (n + 1)) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x)
    (hFg : ∀ t x, F t x = -g x) {β : ℕ → ℝ}
    (hβ : ∀ n < N, ∀ w ∈ segment ℝ (YS n (τ (n + 1))) (Y (n + 1)), ‖g w‖ ≤ β n) :
    ∀ n ≤ N, ℰ (Y n) ≤ ℰ (Y 0) + (∑ k ∈ Finset.range n, β k) * ϑ := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < N := Nat.lt_of_succ_le hn
    have h1 := ((hstep n hn').energy_le_add (hτ n hn') hℰ hFg (hβ n hn')).2
    have h2 := ih hn'.le
    rw [Finset.sum_range_succ]
    linarith

/-! ### The starting value of the Galerkin step (Lemma 1, comparison with the BUG S-step) -/

section StartingValue

variable {F : ℝ → E → E} {L : ℝ} {R : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {y z : ℝ → E}

/-- **Starting the Galerkin step at `Y₀` or at `R Y₀`.**  Let `y` and `z` solve the Galerkin
ODE `x' = R F(t, x)` from `y t₀ = Y₀` and `z t₀ = R Y₀`.  Then `(1 - R)(y t - z t) = (1 - R) Y₀`
for all `t`, so `‖Y₀ - R Y₀‖ ≤ ‖y t - z t‖`: if `Y₀` is not in the Galerkin space, the two
flows never meet (the S-step of the BUG integrator of Ceruti–Lubich starts at `P₁ Q₁ Y₀`, which
by this result loses the component `(1 - P₁ Q₁) Y₀` for good; [CerutiKuschLubich2022, §3.1]). -/
theorem galerkin_normal_sub_eq (hR : IsOrthProj R)
    (hy : ODESolution (fun t x => R (F t x)) y t₀ t₁) (hy₀ : y t₀ = Y₀)
    (hz : ODESolution (fun t x => R (F t x)) z t₀ t₁) (hz₀ : z t₀ = R Y₀) :
    ∀ t ∈ Icc t₀ t₁, (y t - z t) - R (y t - z t) = Y₀ - R Y₀ := by
  intro t ht
  have h1 := normal_const_of_deriv_mem_range (G := fun t => F t (y t)) hR hy.cont hy.deriv t ht
  have h2 := hz.galerkin_mem_range hR (by rw [hz₀, hR.idem]) t ht
  rw [hy₀] at h1
  rw [map_sub, h2]
  rw [← h1]
  abel

/-- Quantitative form of `galerkin_normal_sub_eq`: `‖Y₀ - R Y₀‖ ≤ ‖y t - z t‖`. -/
theorem norm_normal_le_galerkin_sub (hR : IsOrthProj R)
    (hy : ODESolution (fun t x => R (F t x)) y t₀ t₁) (hy₀ : y t₀ = Y₀)
    (hz : ODESolution (fun t x => R (F t x)) z t₀ t₁) (hz₀ : z t₀ = R Y₀) :
    ∀ t ∈ Icc t₀ t₁, ‖Y₀ - R Y₀‖ ≤ ‖y t - z t‖ := by
  intro t ht
  rw [← galerkin_normal_sub_eq hR hy hy₀ hz hz₀ t ht]
  exact hR.norm_sub_le _

/-- **The S-step from `R Y₀` equals the Galerkin flow from `Y₀` exactly when `Y₀ ∈ range R`**
(for Lipschitz `F`).  For the rank-adaptive integrator `R = P₁ Q₁` fixes `Y₀` (Lemma 1 of
[CerutiKuschLubich2022]), so its S-step is the Galerkin flow from `Y₀` itself
(`IsRankAdaptiveBUGStep.eqOn_of_start`). -/
theorem galerkin_eqOn_iff (hR : IsOrthProj R) (hF : IsLipschitzField F L) (hL : 0 ≤ L)
    (h01 : t₀ ≤ t₁) (hy : ODESolution (fun t x => R (F t x)) y t₀ t₁) (hy₀ : y t₀ = Y₀)
    (hz : ODESolution (fun t x => R (F t x)) z t₀ t₁) (hz₀ : z t₀ = R Y₀) :
    EqOn y z (Icc t₀ t₁) ↔ R Y₀ = Y₀ := by
  constructor
  · intro h
    have h' := h ⟨le_rfl, h01⟩
    rw [hy₀, hz₀] at h'
    exact h'.symm
  · intro h
    exact hy.eqOn hz (hF.comp_contraction R hR.norm_le) hL (by rw [hy₀, hz₀, h])

end StartingValue

/-- **The rank-adaptive S-step is the Galerkin flow from `Y₀`** (consequence of Lemma 1 of
[CerutiKuschLubich2022]): any solution `y` of `y' = P₁ Q₁ F(t, y)` with `y t₀ = Y₀` coincides with
the S-step `YS` on `[t₀, t₁]` (for Lipschitz `F`), so the untruncated result is `Ŷ₁ = y t₁`. -/
theorem IsRankAdaptiveBUGStep.eqOn_of_start {F : ℝ → E → E} {ε ϑ L : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} {Y₁ : E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁)
    (hF : IsLipschitzField F L) (hL : 0 ≤ L) (h01 : t₀ ≤ t₁) {y : ℝ → E}
    (hy : ODESolution (fun t x => P₁ (Q₁ (F t x))) y t₀ t₁) (hy₀ : y t₀ = Y₀) :
    EqOn y YS (Icc t₀ t₁) :=
  (galerkin_eqOn_iff (R := P₁ * Q₁) hs.galerkinProj hF hL h01 hy hy₀ hs.sSol hs.sStart).2
    hs.galerkin_fix

/-! ### General augmented Galerkin steps (Tucker tensors, [CerutiKuschLubich2022, §4.2])

The structure-preservation proofs of §3 of [CerutiKuschLubich2022] only use that the Galerkin space
(an orthogonal projector `R`) contains `Y₀` and that the Galerkin step is followed by a
truncation.  For the rank-adaptive Tucker integrator (§4) `R = ∏ᵢ P̂ᵢ` is the product of the
commuting mode projectors onto the augmented bases `Ûᵢ ⊇ (Kᵢ(t₁), U⁰ᵢ)`, each of which fixes
`Y₀` (`list_prod_apply_eq_self`).  We state Theorems 4, 5 and 7 in this generality, which gives
the corresponding claims of §4.2 ("conservation of norm up to the truncation tolerance", "decrease
of the functional in gradient systems", "near-conservation of energy"). -/

/-- One augmented Galerkin step with truncation: the Galerkin space (`range R`, `R` an orthogonal
projector) contains `Y₀`, the S-step is `YS' = R F(t, YS)`, `YS t₀ = R Y₀`, and the truncation
satisfies `‖Y₁ - YS t₁‖ ≤ ϑ`. -/
structure IsAugmentedGalerkinStep (F : ℝ → E → E) (ϑ : ℝ) (R : E →L[ℝ] E) (t₀ t₁ : ℝ) (Y₀ : E)
    (YS : ℝ → E) (Y₁ : E) : Prop where
  proj : IsOrthProj R
  fix : R Y₀ = Y₀
  sSol : ODESolution (fun t x => R (F t x)) YS t₀ t₁
  sStart : YS t₀ = R Y₀
  trunc : ‖Y₁ - YS t₁‖ ≤ ϑ

/-- A product of maps each fixing `Y₀` fixes `Y₀` (the Tucker Galerkin projector
`∏ᵢ P̂ᵢ` fixes `Y₀` when every augmented mode basis contains the old one). -/
lemma list_prod_apply_eq_self {l : List (E →L[ℝ] E)} {Y₀ : E} (h : ∀ P ∈ l, P Y₀ = Y₀) :
    l.prod Y₀ = Y₀ := by
  induction l with
  | nil => rfl
  | cons P l ih =>
    rw [List.prod_cons]
    change P (l.prod Y₀) = Y₀
    rw [ih fun Q hQ => h Q (List.mem_cons_of_mem P hQ), h P List.mem_cons_self]

/-- A rank-adaptive BUG step is an augmented Galerkin step with `R = P₁ Q₁`. -/
theorem IsRankAdaptiveBUGStep.toAugmentedGalerkinStep {F : ℝ → E → E} {ε ϑ : ℝ}
    {P₀ Q₀ P₁ Q₁ : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YK YL YS : ℝ → E} {Y₁ : E}
    (hs : IsRankAdaptiveBUGStep F ε ϑ P₀ Q₀ P₁ Q₁ t₀ t₁ Y₀ YK YL YS Y₁) :
    IsAugmentedGalerkinStep F ϑ (P₁ * Q₁) t₀ t₁ Y₀ YS Y₁ where
  proj := hs.galerkinProj
  fix := hs.galerkin_fix
  sSol := hs.sSol
  sStart := hs.sStart
  trunc := hs.trunc

namespace IsAugmentedGalerkinStep

variable {F : ℝ → E → E} {ϑ : ℝ} {R : E →L[ℝ] E} {t₀ t₁ : ℝ} {Y₀ : E} {YS : ℝ → E} {Y₁ : E}
  {ℰ : E → ℝ} {g : E → E}

/-- Lemma 1 of [CerutiKuschLubich2022] for a general augmented Galerkin step: `YS t₀ = Y₀`. -/
theorem start_eq (hs : IsAugmentedGalerkinStep F ϑ R t₀ t₁ Y₀ YS Y₁) : YS t₀ = Y₀ :=
  hs.sStart.trans hs.fix

/-- **Norm conservation up to truncation** ([CerutiKuschLubich2022, Thm. 4] and §4.2): if
`⟪F(t, Y), Y⟫ = 0` on `range R`, then `‖Ŷ₁‖ = ‖Y₀‖` and `|‖Y₁‖ - ‖Y₀‖| ≤ ϑ`. -/
theorem abs_norm_sub_le (hs : IsAugmentedGalerkinStep F ϑ R t₀ t₁ Y₀ YS Y₁) (h01 : t₀ ≤ t₁)
    (hF : ∀ t x, R x = x → ⟪F t x, x⟫ = 0) : ‖YS t₁‖ = ‖Y₀‖ ∧ |‖Y₁‖ - ‖Y₀‖| ≤ ϑ := by
  have h0 : R (YS t₀) = YS t₀ := by rw [hs.start_eq, hs.fix]
  have h := hs.sSol.galerkin_norm_eq' hs.proj h0 hF t₁ ⟨h01, le_rfl⟩
  rw [hs.start_eq] at h
  refine ⟨h, ?_⟩
  rw [← h]
  exact (abs_norm_sub_norm_le _ _).trans hs.trunc

/-- **Energy decrease up to truncation for gradient systems** ([CerutiKuschLubich2022, Thm. 5] and
§4.2): for `F = -∇ℰ`, `α² ≤ ‖R ∇ℰ(YS t)‖²` along the S-step and `‖∇ℰ‖ ≤ β` on `[Ŷ₁, Y₁]`,
`ℰ(Y₁) ≤ ℰ(Y₀) - α² (t₁ - t₀) + β ϑ`. -/
theorem energy_le (hs : IsAugmentedGalerkinStep F ϑ R t₀ t₁ Y₀ YS Y₁) (h01 : t₀ ≤ t₁)
    (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) (hFg : ∀ t x, F t x = -g x) {α : ℝ}
    (hα : ∀ t ∈ Ico t₀ t₁, α ^ 2 ≤ ‖R (g (YS t))‖ ^ 2) {β : ℝ}
    (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    ℰ Y₁ ≤ ℰ Y₀ - α ^ 2 * (t₁ - t₀) + β * ϑ := by
  have hfun : (fun t x => R (F t x)) = fun _ x => -R (g x) := by
    funext t x
    rw [hFg, map_neg]
  have hy : ODESolution (fun _ x => -R (g x)) YS t₀ t₁ := hfun ▸ hs.sSol
  have h := hy.truncated_energy_le_gradFlow hs.proj hℰ h01 hα hs.trunc hβ
  rwa [hs.start_eq] at h

/-- **Energy conservation up to truncation** ([CerutiKuschLubich2022], Theorems 6–7 and §4.2): for
`F = J ∇ℋ` with `J` skew and commuting with `R`, `ℋ(Ŷ₁) = ℋ(Y₀)` and `|ℋ(Y₁) - ℋ(Y₀)| ≤ β ϑ`
if `‖∇ℋ‖ ≤ β` on `[Ŷ₁, Y₁]`. -/
theorem energy_sub_le_of_skew (hs : IsAugmentedGalerkinStep F ϑ R t₀ t₁ Y₀ YS Y₁)
    (h01 : t₀ ≤ t₁) (hℰ : ∀ x, HasFDerivAt ℰ (innerSL ℝ (g x)) x) {J : E →L[ℝ] E}
    (hJ : ∀ z, ⟪J z, z⟫ = 0) (hJR : ∀ z, J (R z) = R (J z)) (hFJ : ∀ t x, F t x = J (g x))
    {β : ℝ} (hβ : ∀ w ∈ segment ℝ (YS t₁) Y₁, ‖g w‖ ≤ β) :
    ℰ (YS t₁) = ℰ Y₀ ∧ |ℰ Y₁ - ℰ Y₀| ≤ β * ϑ := by
  have h1 := hs.sSol.galerkin_energy_eq_of_skew hs.proj hℰ hJ hJR hFJ t₁ ⟨h01, le_rfl⟩
  have h2 := hs.sSol.truncated_energy_sub_le_of_skew hs.proj hℰ hJ hJR hFJ h01 hs.trunc hβ
  rw [hs.start_eq] at h1 h2
  exact ⟨h1, h2⟩

end IsAugmentedGalerkinStep

/-! ### Satisfiability of the hypotheses -/

section Examples

/-- The hypotheses of one rank-adaptive step are jointly satisfiable with a nonzero vector
field and a nontrivial truncation: on `ℝ`, `F(t, y) = 1`, all projectors the identity,
`Y₀ = 0`, all substep trajectories `t ↦ t` on `[0, 1]` (so `Ŷ₁ = 1`), `ε = 0`, and the
truncation `Y₁ = 1/2` with tolerance `ϑ = 1/2`. -/
theorem constStep : IsRankAdaptiveBUGStep (E := ℝ) (fun _ _ => 1) 0 (1 / 2) 1 1 1 1 0 1 0
    (fun t => t) (fun t => t) (fun t => t) (1 / 2) where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart := rfl
  kCap := rfl
  kNormal _ _ := by simp
  lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  lStart := rfl
  lCap := rfl
  lNormal _ _ := by simp
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  sStart := rfl
  augP := rfl
  augQ := rfl
  trunc := by norm_num

/-- `ℰ(y) = -y` has gradient `-1` on `ℝ`. -/
lemma hasFDerivAt_neg_real (x : ℝ) :
    HasFDerivAt (fun y : ℝ => -y) (innerSL ℝ (-1 : ℝ)) x := by
  have h : innerSL ℝ (-1 : ℝ) = -ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp
  rw [h]
  exact (hasFDerivAt_id x).neg

/-- Theorem 5 applies to `constStep` viewed as the gradient system `F = -∇ℰ`, `ℰ(y) = -y`, with
`α = 1` and `β = 1`; the bound `ℰ(Y₁) ≤ ℰ(Y₀) - α² h + β ϑ = -1/2` is attained. -/
example : -(1 / 2 : ℝ) ≤ -0 - 1 ^ 2 * (1 - 0) + 1 * (1 / 2) :=
  constStep.energy_le (ℰ := fun y : ℝ => -y) (g := fun _ => -1) zero_le_one hasFDerivAt_neg_real
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)

/-- The hypotheses of `rankAdaptiveBUG_global_error` are jointly satisfiable: on `ℝ` with
`F(t, y) = 1` (`L = 0`, `B = 1`), step size `h = 1`, three steps, exact solution `A t = t`,
numerical values `Y n = n`, all projectors the identity and all substep trajectories and exact
flows `t ↦ t`, `ϑ = 0`. -/
example : ∀ n ≤ 3, ‖((n : ℕ) : ℝ) - (0 + n * 1)‖ ≤ Real.exp (0 * (n * 1)) *
    (‖((0 : ℕ) : ℝ) - 0‖ + n * (1 * (bugC₁ 0 1 * 0 + bugC₂ 0 1 1 * 1) + 0)) :=
  rankAdaptiveBUG_global_error (E := ℝ) (F := fun _ _ => 1) (L := 0) (B := 1) (ε := 0)
    (ϑ := 0) (fun _ _ _ => by simp) le_rfl (fun _ _ => by simp) (t₀ := 0) (h := 1) (H := 1)
    zero_le_one le_rfl (N := 3) (A := fun t => t)
    (odeSolution_id_of_eq_one (fun _ _ => rfl) _ _) (P := fun _ => 1) (Q := fun _ => 1)
    (Pa := fun _ => 1) (Qa := fun _ => 1) (Y := fun n => (n : ℝ))
    (YK := fun _ t => t) (YL := fun _ t => t) (YS := fun _ t => t) (Φ := fun _ t => t)
    (fun n _ => {
      projP₀ := IsOrthProj.one
      projQ₀ := IsOrthProj.one
      projP₁ := IsOrthProj.one
      projQ₁ := IsOrthProj.one
      comm₁ := fun _ => rfl
      kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      kStart := by simp
      kCap := rfl
      kNormal := fun _ _ => by simp
      lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      lStart := by simp
      lCap := rfl
      lNormal := fun _ _ => by simp
      sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
      sStart := by simp
      augP := rfl
      augQ := rfl
      trunc := by simp })
    (fun _ _ => odeSolution_id_of_eq_one (fun _ _ => by simp) _ _)
    (fun n _ => by simp)

/-- Multiplication by `-i`, as a real-linear map on `ℂ` (the real formulation of the
Schrödinger right-hand side `-i H[Y]` with `H = 1`). -/
noncomputable def negIMul : ℂ →L[ℝ] ℂ := (-Complex.I) • ContinuousLinearMap.id ℝ ℂ

lemma negIMul_apply (z : ℂ) : negIMul z = -Complex.I * z := by
  simp only [negIMul, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, neg_mul]

/-- Multiplication by `-i` is skew for the real inner product `⟪w, z⟫ = Re (z w̄)` on `ℂ`. -/
lemma negIMul_skew (z : ℂ) : ⟪negIMul z, z⟫ = 0 := by
  rw [negIMul_apply, Complex.inner]
  simp only [neg_mul, map_neg, map_mul, Complex.conj_I, neg_neg, Complex.mul_re, Complex.I_re,
    Complex.conj_re, zero_mul, Complex.I_im, Complex.conj_im, mul_neg, one_mul, sub_neg_eq_add,
    zero_add, Complex.mul_im, neg_zero]
  ring

/-- The rotation `t ↦ e^{-i t}` solves `y' = -i y`. -/
lemma odeSolution_rot {f : ℝ → ℂ → ℂ} (hf : ∀ t z, f t z = -Complex.I * z) (a b : ℝ) :
    ODESolution f (fun t : ℝ => Complex.exp (-Complex.I * t)) a b := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * t))
      (f t (Complex.exp (-Complex.I * t))) t := by
    intro t
    have h1 : HasDerivAt (fun w : ℂ => Complex.exp (-Complex.I * w))
        (Complex.exp (-Complex.I * t) * (-Complex.I * 1)) t :=
      ((hasDerivAt_id (t : ℂ)).const_mul (-Complex.I)).cexp
    rw [hf]
    convert h1.comp_ofReal using 1
    ring
  exact ⟨fun t _ => (hd t).continuousAt.continuousWithinAt, fun t _ => (hd t).hasDerivWithinAt⟩

lemma norm_exp_neg_I_mul (t : ℝ) : ‖Complex.exp (-Complex.I * t)‖ = 1 := by
  have h : -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A **non-trivial conservative rank-adaptive step** (real formulation of a Schrödinger
equation, `E = ℂ` as a real inner product space): `F(t, z) = -i z` (`J = -i`, `H = 1`), all
projectors the identity, `Y₀ = 1`, all substep trajectories `t ↦ e^{-i t}` on `[0, 1]`, `ε = 0`,
and the truncation `Y₁ = Ŷ₁ / 2` with tolerance `ϑ = 1/2`.  This shows that the hypotheses of
Theorems 4, 6 and 7 are jointly satisfiable with a nonzero, norm-conserving field. -/
theorem rotStep : IsRankAdaptiveBUGStep (E := ℂ) (fun _ z => negIMul z) 0 (1 / 2) 1 1 1 1 0 1 1
    (fun t : ℝ => Complex.exp (-Complex.I * t)) (fun t : ℝ => Complex.exp (-Complex.I * t))
    (fun t : ℝ => Complex.exp (-Complex.I * t))
    ((1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))) where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_rot (fun _ z => by simp [negIMul_apply]) _ _
  kStart := by simp
  kCap := rfl
  kNormal _ _ := by simp
  lSol := odeSolution_rot (fun _ z => by simp [negIMul_apply]) _ _
  lStart := by simp
  lCap := rfl
  lNormal _ _ := by simp
  sSol := odeSolution_rot (fun _ z => by simp [negIMul_apply]) _ _
  sStart := by simp
  augP := rfl
  augQ := rfl
  trunc := by
    have h : (1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))
        - Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))
        = (-(1 / 2) : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)) := by
      module
    rw [h, norm_smul, norm_exp_neg_I_mul]
    norm_num

/-- Theorem 4 applies to `rotStep`: the untruncated step conserves the norm exactly. -/
example : ‖Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))‖ = ‖(1 : ℂ)‖ :=
  rotStep.norm_untruncated_eq zero_le_one fun _ x _ => negIMul_skew x

/-- Theorem 6 applies to `rotStep` with `J = -i` and `H = 1`. -/
example : |⟪(1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)),
      (1 : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)))⟫
      - ⟪(1 : ℂ), (1 : ℂ →L[ℝ] ℂ) 1⟫|
    ≤ ‖(1 : ℂ →L[ℝ] ℂ) ((1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)))
      + (1 : ℂ →L[ℝ] ℂ) (Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)))‖ * (1 / 2) :=
  rotStep.schrodinger_energy_sub_le zero_le_one negIMul_skew (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Theorem 7 applies to `rotStep` with `J = -i` and `ℋ = ‖·‖² / 2` (`∇ℋ = id`): the energy
error is at most `β ϑ` with `β = 1 ≥ ‖∇ℋ‖` on the truncation segment. -/
example : |‖(1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))‖ ^ 2 / 2
      - ‖(1 : ℂ)‖ ^ 2 / 2| ≤ 1 * (1 / 2) := by
  refine rotStep.hamiltonian_energy_sub_le (ℰ := fun z : ℂ => ‖z‖ ^ 2 / 2) (g := id)
    zero_le_one hasFDerivAt_half_norm_sq negIMul_skew (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) fun w hw => ?_
  have h1 : Complex.exp (-Complex.I * ((1 : ℝ) : ℂ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_exp_neg_I_mul]
  have h2 : (1 / 2 : ℝ) • Complex.exp (-Complex.I * ((1 : ℝ) : ℂ))
      ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_exp_neg_I_mul]
    norm_num
  have h3 := (convex_closedBall (0 : ℂ) 1).segment_subset h1 h2 hw
  rwa [mem_closedBall_zero_iff] at h3

/-- The hypotheses of an inexact rank-adaptive step are jointly satisfiable with nonzero
substep errors: on `ℝ` with `F(t, y) = 1`, all projectors the identity, `Y₀ = 0`, exact substep
trajectories `t ↦ t` on `[0, 1]`, computed values `K₁ = L₁ = Ŷ₁ = 5/4` (local errors
`η = 1/4`) and truncation `Y₁ = 1` (`ϑ = 1/4`). -/
example : IsInexactRankAdaptiveBUGStep (E := ℝ) (fun _ _ => 1) 0 (1 / 4) (1 / 4) 1 1 1 1 0 1 0
    (fun t => t) (fun t => t) (fun t => t) (5 / 4) (5 / 4) (5 / 4) 1 where
  projP₀ := IsOrthProj.one
  projQ₀ := IsOrthProj.one
  projP₁ := IsOrthProj.one
  projQ₁ := IsOrthProj.one
  comm₁ _ := rfl
  kSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  kStart := rfl
  kApprox := by norm_num
  kCap := rfl
  kNormal _ _ := by simp
  lSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  lStart := rfl
  lApprox := by norm_num
  lCap := rfl
  lNormal _ _ := by simp
  augP := rfl
  augQ := rfl
  sSol := odeSolution_id_of_eq_one (fun _ _ => by simp) _ _
  sStart := rfl
  sApprox := by norm_num
  trunc := by norm_num

end Examples

end LeanDLRA

import LeanDLRA.Integrators.BUG
import LeanDLRA.Integrators.ParallelBUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Kinetic.Defs

/-!
# Results of arXiv 2502.20883: a parallel, energy-stable low-rank integrator for radiative transfer

This module formalizes the analysis of Patwardhan and Kusch for the concrete fully discrete
macro–micro scheme (3.3) with the Stefan–Boltzmann closure, not an abstract core.  One coordinate
direction of the staggered grid is a `Stencil`, with the operators `δ⁰`, `𝒟⁰`, `𝒟^±` and the upwind
flux `ℒ`; `periodicX`, `periodicY` are the two directions of the periodic staggered grid, and the
`example`s after `periodic_inner` check that the operators are those of the paper.  A `Setup` is
the data of the scheme, `IsStep` one step of (3.3) and `IsMacroStep` its part (3.3b), (3.3c).  The
module proves local and global mass conservation (`theorem_1`, `theorem_1_mass`, and for `g^{n+1} =
X S Vᵀ`, `theorem_4`, `theorem_4_mass`), the asymptotic-preserving property of the full-rank scheme
as a true limit `ε → 0`, for one step and along trajectories (`theorem_2_step`, `theorem_2`) and of
the parallel BUG scheme (`theorem_5`), nonlinear energy stability under the mixed CFL condition
(3.9) with the constants of the paper (`theorem_3`, `theorem_3_antitone`), and Lemma 9 (`lemma_9`),
and it refutes Lemma 7 of the paper (`lemma_7_iff`, `lemma_7_counterexample`).

## Differences from the paper

* Boundary conditions.  Zero and periodic boundary conditions are treated at once: a face without
  two neighbours is not `IsInner` and carries `g = 0` (no such face on the periodic grid,
  `periodic_inner`; `zeroStencil_isInner_iff` shows what happens with zero boundary conditions).
  The paper's reflection–transmission conditions (4.5) are not formalized.  Theorems 2 and 5 assume
  that (3.3a), resp. (4.2)–(4.4), hold on all faces.
* Lemma 7, `φᵀ Q_v w wᵀ Q_v φ ≤ π φᵀ |Q_v| M² φ`, is stated without proof in the paper.  It is
  equivalent to `∑ w |Ω_v| ≤ π` (`lemma_7_iff`) and **false** for the tensorized Gauss–Legendre
  rule of order two (`lemma_7_counterexample`), although that rule has all the moments asked for
  (`s2_moments`).  The proof of Theorem 3 uses Lemma 7 only with the factor `Δt/(4π)` in (A.18),
  and leaves room for a weaker estimate.  `moment_sq_le` bounds `(wᵀ Q_v φ)²` with the weight `3
  |Ω| - 2 Ω²` in place of `|Ω|`, under `∑ w |Ω| / (3 - 2|Ω|) ≤ π`, which follows from the second
  moments of the rule.  So Theorem 3 holds as stated, with the same CFL constant, for every rule
  with the moments of `IsQuadrature`, `IsSecondOrder`.  `theorem_3_of_lemma_7` is the variant under
  the condition of Lemma 7 instead of the second moments.
* Theorem 3: the hypotheses left implicit are stated, namely `⟨gⁿ⟩ = 0`, `T ≥ 0`, `T' ≥ 0` (Lemma
  9), `σ^t ≥ σ₀ ≥ 0`, `σ^a ≥ 0`, `|Ω_v| ≤ 1`, `w ≥ 0`, and the first moments of the rule. `T' ≥ 0`
  does not follow from the scheme.  `⟨g^{n+1}⟩ = 0` is derived, not assumed.  In the printed CFL
  condition the minimum is over the `ℓ` with `Ω_x^ℓ, Ω_y^ℓ ≠ 0`; here each bound is imposed where
  its own denominator does not vanish.  Lemma 8 is applied only when the coefficient `3 c Δt - ε
  Δv` is positive; the paper applies it regardless, which is harmless.  The printed third and
  fourth relation of Lemma 1 have swapped indices, and in (A.14) the term `ℒ g^{n+1}` should read
  `ℒ gⁿ`.  Lemmas 2 to 6 and Lemma 8 are absorbed in `Stencil.upwind_lower` and
  `Stencil.sum_D0_sq_le`.
* Theorem 2: the paper sets `ε = 0` formally.  Here data that converge as `ε → 0` at fixed `Δt` are
  given, and it is proved that `g^{n+1}` converges to `limitFlux`, and that every family of
  solutions with `T^{n+1} ≥ 0` for small `ε` converges to a solution of (3.6) (`macro_limit`,
  `tendsto_of_expanding`).  Hypotheses: `σ^t ≥ σ₀ > 0`, `σ^a > 0`, the second moments of the rule.
* Theorem 5: the limit is a true limit, the bases `X̃`, `Ṽ` may depend on `ε`, and the rank
  condition on `Xᵀ Σᵗ X` that the proof of the paper assumes is derived from `σ^t > 0`.  The
  conservative truncation is modelled by the inequality `htr`, the common property of the
  truncations of the paper's references (`conservative_right`): the truncation error is at most the
  part of the solution outside the preserved directions.  The range conditions on `V` matter only
  for the preserved directions `W`.  The data `X`, `S`, `V`, `h`, `T` at time `tₙ` are fixed, as in
  the paper's proof.  The algebra of the augmentation is `matrix_parallelBUG_eq`.
* Theorem 6 of the paper, which is not part of this slice, is not formalized.

Non-vacuity: `theorem_3_nonvacuous` (also for Theorem 2, with a step size independent of `ε`),
`theorem_5_nonvacuous`, and the solvability results `exists_isMacroStep`, `exists_isStep`,
`exists_isParallelStep`.

Core vocabulary: a rule with `IsQuadrature` and positive weights gives core quadratures
`Kinetic.Quadrature` of `LeanDLRA/Kinetic/Defs.lean` with the weights `w_ℓ / (2π)`
(`Setup.IsQuadrature.toQuadratureX`, `Setup.IsQuadrature.toQuadratureY`).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace Matrix

namespace LeanDLRA.Literature.P2502_20883

open scoped Real

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

noncomputable section

variable {C F ι : Type*}

/-- One coordinate direction `v ∈ {x, y}` of a staggered grid: `C` is the set of cell nodes
(centres and corners, the red points of Figure 1 of the paper) and `F` the set of faces (the blue
points).  A cell node `c` has the face `right c` in front of it and the face `left c` behind it; a
face `f` has the cell node `ahead f` in front of it and `behind f` behind it. -/
structure Stencil (C F : Type*) where
  /-- The face in front of the cell node `c`. -/
  right : C → F
  /-- The face behind the cell node `c`. -/
  left : C → F
  /-- The cell node in front of the face `f`. -/
  ahead : F → C
  /-- The cell node behind the face `f`. -/
  behind : F → C
  ahead_left : ∀ c, ahead (left c) = c
  behind_right : ∀ c, behind (right c) = c
  /-- The mesh width `Δv`. -/
  Δ : ℝ

namespace Stencil

variable (s : Stencil C F)

/-- A face that really has both of its cell neighbours in this direction.  On a periodic grid every
face is inner; with zero boundary conditions the other faces carry `g = 0`. -/
def IsInner (f : F) : Prop := s.left (s.ahead f) = f ∧ s.right (s.behind f) = f

/-- The next face of the same family: `α ↦ α + 1`. -/
def next (f : F) : F := s.right (s.ahead f)

/-- The previous face of the same family: `α ↦ α - 1`. -/
def prev (f : F) : F := s.left (s.behind f)

/-- `δ⁰_v`: from cell nodes to faces, `(δ⁰ u)_f = (u_{f + ½} - u_{f - ½}) / Δv`. -/
def δ (u : C → ℝ) (f : F) : ℝ := (u (s.ahead f) - u (s.behind f)) / s.Δ

/-- `𝒟⁰_v`: from faces to cell nodes, `(𝒟⁰ g)_c = (g_{c + ½} - g_{c - ½}) / Δv`. -/
def D0 (g : F → ℝ) (c : C) : ℝ := (g (s.right c) - g (s.left c)) / s.Δ

/-- `𝒟⁺_v`: `(g_{f + 1} - g_f) / Δv`. -/
def Dp (g : F → ℝ) (f : F) : ℝ := (g (s.next f) - g f) / s.Δ

/-- `𝒟⁻_v`: `(g_f - g_{f - 1}) / Δv`. -/
def Dm (g : F → ℝ) (f : F) : ℝ := (g f - g (s.prev f)) / s.Δ

/-- The upwind flux `ℒ_v` in one discrete direction: `Q⁻ 𝒟⁺ + Q⁺ 𝒟⁻` with `Q^± = (Ω ± |Ω|) / 2`. -/
def upwind (Ω : ℝ) (g : F → ℝ) (f : F) : ℝ :=
  (Ω - |Ω|) / 2 * s.Dp g f + (Ω + |Ω|) / 2 * s.Dm g f

/-- The map `left` is injective, as `ahead` is a left inverse. -/
theorem left_injective : Function.Injective s.left :=
  Function.LeftInverse.injective s.ahead_left

/-- The map `right` is injective, as `behind` is a left inverse. -/
theorem right_injective : Function.Injective s.right :=
  Function.LeftInverse.injective s.behind_right

/-- `𝒟⁰` at a cell node is `𝒟⁺` at the face behind it. -/
theorem D0_eq_Dp (g : F → ℝ) (c : C) : s.D0 g c = s.Dp g (s.left c) := by
  simp [D0, Dp, next, s.ahead_left]

/-- `𝒟⁰` at a cell node is `𝒟⁻` at the face in front of it. -/
theorem D0_eq_Dm (g : F → ℝ) (c : C) : s.D0 g c = s.Dm g (s.right c) := by
  simp [D0, Dm, prev, s.behind_right]

/-- The upwind flux is additive. -/
theorem upwind_add (Ω : ℝ) (a b : F → ℝ) (f : F) :
    s.upwind Ω (fun f => a f + (b f - a f)) f =
      s.upwind Ω a f + s.upwind Ω (fun f => b f - a f) f := by
  simp only [upwind, Dp, Dm]
  ring

variable [Fintype C] [Fintype F]

/-- Reindexing a sum over the faces by `left`, for a function that vanishes on non-inner faces. -/
theorem sum_left {a : F → ℝ} (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ c, a (s.left c) = ∑ f, a f :=
  Fintype.sum_of_injective s.left s.left_injective _ _
    (fun f hf => ha f fun h => hf ⟨_, h.1⟩) fun _ => rfl

/-- Reindexing a sum over the faces by `right`, for a function that vanishes on non-inner faces. -/
theorem sum_right {a : F → ℝ} (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ c, a (s.right c) = ∑ f, a f :=
  Fintype.sum_of_injective s.right s.right_injective _ _
    (fun f hf => ha f fun h => hf ⟨_, h.2⟩) fun _ => rfl

/-- The shift `next` in a sum, written over the cell nodes. -/
theorem sum_mul_next {a : F → ℝ} (b : F → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * b (s.next f) = ∑ c, a (s.left c) * b (s.right c) := by
  rw [← s.sum_left (a := fun f => a f * b (s.next f)) fun f hf => by simp [ha f hf]]
  simp [next, s.ahead_left]

/-- The shift `prev` in a sum, written over the cell nodes. -/
theorem sum_mul_prev {a : F → ℝ} (b : F → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * b (s.prev f) = ∑ c, a (s.right c) * b (s.left c) := by
  rw [← s.sum_right (a := fun f => a f * b (s.prev f)) fun f hf => by simp [ha f hf]]
  simp [prev, s.behind_right]

/-- **Lemma 1 of arXiv 2502.20883** (summation by parts).  The four relations of the paper, which
differ only by the family of faces, are one statement here; the printed third and fourth relation
have their indices swapped.  The hypothesis says that `a` vanishes on faces without two neighbours
(no condition on a periodic grid). -/
theorem sum_mul_δ {a : F → ℝ} (u : C → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.δ u f = -∑ c, s.D0 a c * u c := by
  have h1 : ∑ f, a f * u (s.ahead f) = ∑ c, a (s.left c) * u c := by
    rw [← s.sum_left (a := fun f => a f * u (s.ahead f)) fun f hf => by simp [ha f hf]]
    simp [s.ahead_left]
  have h2 : ∑ f, a f * u (s.behind f) = ∑ c, a (s.right c) * u c := by
    rw [← s.sum_right (a := fun f => a f * u (s.behind f)) fun f hf => by simp [ha f hf]]
    simp [s.behind_right]
  have e1 : ∀ f, a f * s.δ u f = (a f * u (s.ahead f) - a f * u (s.behind f)) / s.Δ := fun f => by
    simp only [δ]; ring
  have e2 : ∀ c, s.D0 a c * u c = (a (s.right c) * u c - a (s.left c) * u c) / s.Δ := fun c => by
    simp only [D0]; ring
  simp only [e1, e2, ← Finset.sum_div, Finset.sum_sub_distrib, h1, h2]
  ring

/-- The discrete divergence has zero sum (the telescoping behind Theorems 1 and 4). -/
theorem sum_D0_eq_zero {a : F → ℝ} (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ c, s.D0 a c = 0 := by
  simp only [D0, ← Finset.sum_div, Finset.sum_sub_distrib, s.sum_left ha, s.sum_right ha]
  simp

/-- **Lemma 8 of arXiv 2502.20883**, with `𝒟⁺` written through `𝒟⁰ = 𝒟⁺ ∘ left` and without the
weights, which are constants in the sums over faces. -/
theorem sum_D0_sq_le (hΔ : 0 < s.Δ) {a : F → ℝ} (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ c, s.D0 a c ^ 2 ≤ 4 / s.Δ ^ 2 * ∑ f, a f ^ 2 := by
  have h2 : ∀ f, ¬ s.IsInner f → a f ^ 2 = 0 := fun f hf => by simp [ha f hf]
  have key : ∀ c, s.D0 a c ^ 2 ≤ 2 / s.Δ ^ 2 * (a (s.right c) ^ 2 + a (s.left c) ^ 2) := fun c => by
    have h : (a (s.right c) - a (s.left c)) ^ 2 ≤ 2 * (a (s.right c) ^ 2 + a (s.left c) ^ 2) := by
      nlinarith [sq_nonneg (a (s.right c) + a (s.left c))]
    calc s.D0 a c ^ 2 = (a (s.right c) - a (s.left c)) ^ 2 / s.Δ ^ 2 := by
          simp only [D0, div_pow]
      _ ≤ 2 * (a (s.right c) ^ 2 + a (s.left c) ^ 2) / s.Δ ^ 2 := by gcongr
      _ = _ := by ring
  calc ∑ c, s.D0 a c ^ 2 ≤ ∑ c, 2 / s.Δ ^ 2 * (a (s.right c) ^ 2 + a (s.left c) ^ 2) :=
        Finset.sum_le_sum fun c _ => key c
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, s.sum_right h2, s.sum_left h2]
        ring

/-- The term with `𝒟⁺` of the summation by parts (Lemma 2 of arXiv 2502.20883). -/
theorem sum_mul_Dp {a : F → ℝ} (b : F → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.Dp b f = (∑ c, a (s.left c) * b (s.right c) - ∑ f, a f * b f) / s.Δ := by
  have e : ∀ f, a f * s.Dp b f = (a f * b (s.next f) - a f * b f) / s.Δ := fun f => by
    simp only [Dp]; ring
  simp only [e, ← Finset.sum_div, Finset.sum_sub_distrib, s.sum_mul_next b ha]

/-- The term with `𝒟⁻` of the summation by parts (Lemma 2 of arXiv 2502.20883). -/
theorem sum_mul_Dm {a : F → ℝ} (b : F → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.Dm b f = (∑ f, a f * b f - ∑ c, a (s.right c) * b (s.left c)) / s.Δ := by
  have e : ∀ f, a f * s.Dm b f = (a f * b f - a f * b (s.prev f)) / s.Δ := fun f => by
    simp only [Dm]; ring
  simp only [e, ← Finset.sum_div, Finset.sum_sub_distrib, s.sum_mul_prev b ha]

/-- The transport term `⟨a, ℒ b⟩` over the cell nodes. -/
theorem sum_mul_upwind (Ω : ℝ) {a : F → ℝ} (b : F → ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.upwind Ω b f =
      (Ω - |Ω|) / 2 * ((∑ c, a (s.left c) * b (s.right c) - ∑ f, a f * b f) / s.Δ) +
      (Ω + |Ω|) / 2 * ((∑ f, a f * b f - ∑ c, a (s.right c) * b (s.left c)) / s.Δ) := by
  rw [← s.sum_mul_Dp b ha, ← s.sum_mul_Dm b ha, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by simp only [upwind]; ring

/-- The dissipative part of Lemma 6 of arXiv 2502.20883: `⟨a, ℒ a⟩ = (Δ/2) |Ω| ‖𝒟⁺ a‖²`. -/
theorem sum_mul_upwind_self (hΔ : s.Δ ≠ 0) (Ω : ℝ) {a : F → ℝ}
    (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.upwind Ω a f = |Ω| * (s.Δ / 2) * ∑ c, s.D0 a c ^ 2 := by
  have h2 : ∀ f, ¬ s.IsInner f → a f ^ 2 = 0 := fun f hf => by simp [ha f hf]
  have hD : ∑ c, s.D0 a c ^ 2 =
      (2 * ∑ f, a f ^ 2 - 2 * ∑ c, a (s.left c) * a (s.right c)) / s.Δ ^ 2 := by
    have e : ∀ c, s.D0 a c ^ 2 = (a (s.right c) ^ 2 + a (s.left c) ^ 2
        - 2 * (a (s.left c) * a (s.right c))) / s.Δ ^ 2 := fun c => by
      simp only [D0, div_pow]; ring
    simp only [e, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, s.sum_right h2, s.sum_left h2]
    ring
  rw [s.sum_mul_upwind Ω a ha, hD]
  have e : ∑ c, a (s.right c) * a (s.left c) = ∑ c, a (s.left c) * a (s.right c) :=
    Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [e]
  simp only [← sq]
  field_simp
  ring

/-- The cross part of Lemma 6 of arXiv 2502.20883, in the form used for the Young step. -/
theorem sum_mul_upwind_eq {a χ : F → ℝ} (Ω : ℝ) (ha : ∀ f, ¬ s.IsInner f → a f = 0) :
    ∑ f, a f * s.upwind Ω χ f =
      -∑ c, s.D0 a c * ((Ω - |Ω|) / 2 * χ (s.right c) + (Ω + |Ω|) / 2 * χ (s.left c)) := by
  have h0 : ∀ f, ¬ s.IsInner f → a f * χ f = 0 := fun f hf => by simp [ha f hf]
  have e : ∀ c, s.D0 a c * ((Ω - |Ω|) / 2 * χ (s.right c) + (Ω + |Ω|) / 2 * χ (s.left c)) =
      (Ω - |Ω|) / 2 * ((a (s.right c) * χ (s.right c) - a (s.left c) * χ (s.right c)) / s.Δ) +
      (Ω + |Ω|) / 2 * ((a (s.right c) * χ (s.left c) - a (s.left c) * χ (s.left c)) / s.Δ) :=
    fun c => by simp only [D0]; ring
  rw [s.sum_mul_upwind Ω χ ha]
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib,
    s.sum_left h0, s.sum_right h0]
  ring

/-- Lemma 5 and Lemma 6 of arXiv 2502.20883 for one discrete direction: the lower bound for the
transport term.  `β` plays the role of the paper's `α`. -/
theorem upwind_lower (hΔ : s.Δ ≠ 0) (A : ℝ) {β : ℝ} (hβ : 0 < β) (Ω : ℝ) {a b : F → ℝ}
    (ha : ∀ f, ¬ s.IsInner f → a f = 0) (hb : ∀ f, ¬ s.IsInner f → b f = 0) :
    A * (|Ω| * (s.Δ / 2)) * ∑ c, s.D0 a c ^ 2 - β * ∑ f, (b f - a f) ^ 2
        - A ^ 2 * Ω ^ 2 / (4 * β) * ∑ c, s.D0 a c ^ 2 ≤
      A * ∑ f, a f * s.upwind Ω b f := by
  have hχ : ∀ f, ¬ s.IsInner f → (b f - a f) ^ 2 = 0 := fun f hf => by simp [ha f hf, hb f hf]
  have hsplit : ∑ f, a f * s.upwind Ω b f =
      ∑ f, a f * s.upwind Ω a f + ∑ f, a f * s.upwind Ω (fun f => b f - a f) f := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← mul_add, ← s.upwind_add]
    simp
  rw [hsplit, s.sum_mul_upwind_self hΔ Ω ha, s.sum_mul_upwind_eq Ω ha, mul_add]
  suffices h : A * ∑ c, s.D0 a c *
      ((Ω - |Ω|) / 2 * (b (s.right c) - a (s.right c)) +
        (Ω + |Ω|) / 2 * (b (s.left c) - a (s.left c))) ≤
      β * ∑ f, (b f - a f) ^ 2 + A ^ 2 * Ω ^ 2 / (4 * β) * ∑ c, s.D0 a c ^ 2 by
    linarith
  have young : ∀ x y : ℝ, A * (x * (Ω * y)) ≤ β * y ^ 2 + A ^ 2 * Ω ^ 2 / (4 * β) * x ^ 2 := by
    intro x y
    have : β * y ^ 2 + A ^ 2 * Ω ^ 2 / (4 * β) * x ^ 2 - A * (x * (Ω * y)) =
        (2 * β * y - A * Ω * x) ^ 2 / (4 * β) := by
      field_simp
      ring
    have h0 : 0 ≤ (2 * β * y - A * Ω * x) ^ 2 / (4 * β) := by positivity
    linarith
  rw [Finset.mul_sum]
  rcases le_total 0 Ω with hΩ | hΩ
  · rw [← s.sum_left hχ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have := young (s.D0 a c) (b (s.left c) - a (s.left c))
    rw [abs_of_nonneg hΩ]
    calc _ = A * (s.D0 a c * (Ω * (b (s.left c) - a (s.left c)))) := by ring
      _ ≤ _ := this
  · rw [← s.sum_right hχ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have := young (s.D0 a c) (b (s.right c) - a (s.right c))
    rw [abs_of_nonpos hΩ]
    calc _ = A * (s.D0 a c * (Ω * (b (s.right c) - a (s.right c)))) := by ring
      _ ≤ _ := this

end Stencil

/-- The data of the macro–micro scheme (3.3) of arXiv 2502.20883 in the projected two-dimensional
geometry.  The Knudsen number `ε` is not part of the data, since Theorems 2 and 5 let it vary. -/
structure Setup (C F ι : Type*) where
  /-- The stencil of the `x` direction. -/
  x : Stencil C F
  /-- The stencil of the `y` direction. -/
  y : Stencil C F
  /-- The speed of light `c`. -/
  c : ℝ
  /-- The heat capacity `c_ν`. -/
  cν : ℝ
  /-- The radiation constant `a`. -/
  a : ℝ
  /-- The step size `Δt`. -/
  Δt : ℝ
  /-- The quadrature weights `w_ℓ`. -/
  w : ι → ℝ
  /-- The first components `Ω_x^ℓ` of the quadrature points. -/
  Ωx : ι → ℝ
  /-- The second components `Ω_y^ℓ` of the quadrature points. -/
  Ωy : ι → ℝ
  /-- The total cross section `σ^t` on the faces. -/
  σt : F → ℝ
  /-- The absorption cross section `σ^a` on the cell nodes. -/
  σa : C → ℝ

namespace Setup

variable (P : Setup C F ι)

/-- The Stefan–Boltzmann closure `B(T) = (a c / 2π) T⁴`. -/
def B (T : ℝ) : ℝ := P.a * P.c / (2 * π) * T ^ 4

/-- A face on which (3.3a) is imposed.  All faces of a periodic grid are inner; on the others
zero boundary conditions prescribe `g = 0`. -/
def Inner (f : F) : Prop := P.x.IsInner f ∧ P.y.IsInner f

/-- The scalar flux `φ = B(T) + ε² h`. -/
def phi (ε : ℝ) (h T : C → ℝ) (c : C) : ℝ := P.B (T c) + ε ^ 2 * h c

/-- The cell volume `Δζ = Δx Δy`. -/
def Δζ : ℝ := P.x.Δ * P.y.Δ

/-- The function `|Ω| / (3 - 2 |Ω|)`, which replaces `|Ω|` in the estimate that makes Lemma 7 of the
paper superfluous, see `moment_sq_le`. -/
def moderate (Ω : ℝ) : ℝ := |Ω| / (3 - 2 * |Ω|)

variable [Fintype ι]

/-- `(I - (1/2π) 𝟙 wᵀ) v`. -/
def meanFree (v : ι → ℝ) (ℓ : ι) : ℝ := v ℓ - 1 / (2 * π) * ∑ ℓ', P.w ℓ' * v ℓ'

/-- `(ℒ_x + ℒ_y) g`, the sum of the upwind fluxes. -/
def transport (g : F → ι → ℝ) (f : F) (ℓ : ι) : ℝ :=
  P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f + P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f

/-- `wᵀ Q_v 𝒟⁰_v g` at a cell node. -/
def wQD (s : Stencil C F) (Ω : ι → ℝ) (g : F → ι → ℝ) (c : C) : ℝ :=
  ∑ ℓ, P.w ℓ * Ω ℓ * s.D0 (fun f => g f ℓ) c

/-- The macro part (3.3b), (3.3c) of the scheme.  It involves `g` only through `g'`, the new value,
which is what makes Theorem 4 of the paper independent of how `g'` is computed. -/
structure IsMacroStep (ε : ℝ) (h T : C → ℝ) (g' : F → ι → ℝ) (h' T' : C → ℝ) : Prop where
  h_eq : ∀ c, ε ^ 2 / (P.c * P.Δt) * (h' c - h c) + 1 / (P.c * P.Δt) * (P.B (T' c) - P.B (T c))
    + 1 / (2 * π) * P.wQD P.x P.Ωx g' c + 1 / (2 * π) * P.wQD P.y P.Ωy g' c = -P.σa c * h' c
  T_eq : ∀ c, P.cν / P.Δt * (T' c - T c) = 2 * π * P.σa c * h' c

/-- The micro equation (3.3a) at the face `f` and the direction `ℓ`. -/
def MicroEq (ε : ℝ) (g : F → ι → ℝ) (h T : C → ℝ) (g' : F → ι → ℝ) (f : F) (ℓ : ι) : Prop :=
  ε ^ 2 / (P.c * P.Δt) * (g' f ℓ - g f ℓ) + ε * P.meanFree (P.transport g f) ℓ
    + P.Ωx ℓ * P.x.δ (P.phi ε h T) f + P.Ωy ℓ * P.y.δ (P.phi ε h T) f = -P.σt f * g' f ℓ

/-- One step `(g, h, T) ↦ (g', h', T')` of the full-rank macro–micro scheme (3.3).  The equation
(3.3a) is imposed on inner faces and `g' = 0` on the others (no condition on a periodic grid). -/
structure IsStep (ε : ℝ) (g : F → ι → ℝ) (h T : C → ℝ) (g' : F → ι → ℝ) (h' T' : C → ℝ) : Prop
    extends P.IsMacroStep ε h T g' h' T' where
  g_eq : ∀ f, P.Inner f → ∀ ℓ, P.MicroEq ε g h T g' f ℓ
  wall : ∀ f, ¬ P.Inner f → ∀ ℓ, g' f ℓ = 0

omit [Fintype ι] in
/-- The mass (3.4) of the paper. -/
def mass [Fintype C] (ε : ℝ) (h T : C → ℝ) : ℝ :=
  ∑ c, (2 * π / P.c * P.phi ε h T c + P.cν * T c) * P.Δζ

/-- The energy (3.8) of the paper. -/
def energy [Fintype C] [Fintype F] (ε : ℝ) (g : F → ι → ℝ) (h T : C → ℝ) : ℝ :=
  ∑ c, (1 / P.c * P.B (T c) + ε ^ 2 / P.c * h c) ^ 2 * P.Δζ
    + 1 / (2 * π) * ∑ f, ∑ ℓ, P.w ℓ * (ε / P.c * g f ℓ) ^ 2 * P.Δζ
    + 2 / 5 * ∑ c, (√(P.a * P.cν) / (2 * π) * T c ^ (5 / 2 : ℝ)) ^ 2 * P.Δζ

variable {P}

/-- **Theorem 1 of arXiv 2502.20883** (local mass conservation): the discrete conservation law for
`φ = B + ε² h` and `T`.  It is a rearrangement of (3.3b), (3.3c) and holds for every grid. -/
theorem theorem_1 {ε : ℝ} {h T h' T' : C → ℝ} {g' : F → ι → ℝ}
    (hs : P.IsMacroStep ε h T g' h' T') (c : C) :
    1 / (P.c * P.Δt) * (P.phi ε h' T' c - P.phi ε h T c) + 1 / (2 * π) * P.wQD P.x P.Ωx g' c
        + 1 / (2 * π) * P.wQD P.y P.Ωy g' c = -P.σa c * h' c ∧
      P.cν / P.Δt * (T' c - T c) = 2 * π * P.σa c * h' c := by
  refine ⟨?_, hs.T_eq c⟩
  simp only [phi]
  linear_combination hs.h_eq c

/-- `wᵀ Q 𝒟⁰ g = 𝒟⁰ (wᵀ Q g)`. -/
theorem wQD_eq_D0 (s : Stencil C F) (Ω : ι → ℝ) (g : F → ι → ℝ) (c : C) :
    P.wQD s Ω g c = s.D0 (fun f => ∑ ℓ, P.w ℓ * Ω ℓ * g f ℓ) c := by
  simp only [wQD, Stencil.D0, mul_div_assoc', mul_sub, ← Finset.sum_div, Finset.sum_sub_distrib]

/-- `∑ wᵀ Q 𝒟⁰ g = 0` for zero or periodic boundary conditions, the proof of Theorem 1. -/
theorem sum_wQD [Fintype C] [Fintype F] (s : Stencil C F) (Ω : ι → ℝ) {g : F → ι → ℝ}
    (hg : ∀ f, ¬ s.IsInner f → ∀ ℓ, g f ℓ = 0) : ∑ c, P.wQD s Ω g c = 0 := by
  simp only [wQD_eq_D0]
  exact s.sum_D0_eq_zero fun f hf => by simp [hg f hf]

/-- **Theorem 1 of arXiv 2502.20883**, the conservation of the total mass `mⁿ` of (3.4), for zero
boundary conditions (`g' = 0` on the faces that lack a neighbour) and for periodic ones (no such
faces, see `periodic_inner`).  As in the proof of the paper no sign of `σ^a` is needed. -/
theorem theorem_1_mass [Fintype C] [Fintype F] {ε : ℝ} {h T h' T' : C → ℝ} {g' : F → ι → ℝ}
    (hc : P.c ≠ 0) (hΔt : P.Δt ≠ 0) (hs : P.IsMacroStep ε h T g' h' T')
    (hg' : ∀ f, ¬ P.Inner f → ∀ ℓ, g' f ℓ = 0) : P.mass ε h' T' = P.mass ε h T := by
  have key : ∀ z, 2 * π / P.c * P.phi ε h' T' z + P.cν * T' z =
      2 * π / P.c * P.phi ε h T z + P.cν * T z
        - P.Δt * (P.wQD P.x P.Ωx g' z + P.wQD P.y P.Ωy g' z) := fun z => by
    have e1 := hs.h_eq z
    have e2 := hs.T_eq z
    simp only [phi]
    field_simp at e1 e2 ⊢
    linear_combination e1 + P.c * e2
  have hx := P.sum_wQD P.x P.Ωx (g := g') fun f hf => hg' f fun h => hf h.1
  have hy := P.sum_wQD P.y P.Ωy (g := g') fun f hf => hg' f fun h => hf h.2
  simp only [mass, ← Finset.sum_mul]
  congr 1
  simp only [key, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hx, hy]
  simp

end Setup

/-- **Lemma 9 of arXiv 2502.20883**, for `a, b ≥ 0` instead of `a, b > 0`, by the factorization
`5 a⁴ (a - b) - (a⁵ - b⁵) = (a - b)² (4a³ + 3a²b + 2ab² + b³)` instead of the paper's contradiction
argument. -/
theorem lemma_9 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 4 * (a - b) - 1 / 5 * (a ^ 5 - b ^ 5) ≥ 0 := by
  have e : a ^ 4 * (a - b) - 1 / 5 * (a ^ 5 - b ^ 5) =
      (a - b) ^ 2 * (4 * a ^ 3 + 3 * a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3) / 5 := by ring
  rw [e]
  positivity

namespace Setup

/-- The elementary inequality behind `moment_sq_le`. -/
theorem moderate_mul_add (Ω l D : ℝ) (hΩ : |Ω| ≤ 1) :
    2 * l * (Ω * D) ≤ l ^ 2 * moderate Ω + (3 * |Ω| - 2 * Ω ^ 2) * D ^ 2 := by
  have ht : 0 ≤ |Ω| := abs_nonneg Ω
  have hd : 0 < 3 - 2 * |Ω| := by linarith
  have hd' : 3 - 2 * |Ω| ≠ 0 := hd.ne'
  have hq : 3 * |Ω| - 2 * Ω ^ 2 = |Ω| * (3 - 2 * |Ω|) := by
    rw [← sq_abs Ω]
    ring
  have key₁ : ∀ t d : ℝ, d ≠ 0 → l ^ 2 * (t / d) + t * d * D ^ 2 - 2 * l * (t * D) =
      t / d * (l - d * D) ^ 2 := fun t d hd => by
    field_simp
    ring
  have key₂ : ∀ t d : ℝ, d ≠ 0 → l ^ 2 * (t / d) + t * d * D ^ 2 + 2 * l * (t * D) =
      t / d * (l + d * D) ^ 2 := fun t d hd => by
    field_simp
    ring
  rw [hq, moderate]
  rcases le_total 0 Ω with h0 | h0
  · have e : l ^ 2 * (|Ω| / (3 - 2 * |Ω|)) + |Ω| * (3 - 2 * |Ω|) * D ^ 2 - 2 * l * (|Ω| * D) =
        |Ω| / (3 - 2 * |Ω|) * (l - (3 - 2 * |Ω|) * D) ^ 2 := key₁ _ _ hd'
    have h1 : 0 ≤ |Ω| / (3 - 2 * |Ω|) * (l - (3 - 2 * |Ω|) * D) ^ 2 := by positivity
    have h2 : Ω = |Ω| := (abs_of_nonneg h0).symm
    rw [← e] at h1
    rw [h2, abs_abs]
    linarith
  · have e : l ^ 2 * (|Ω| / (3 - 2 * |Ω|)) + |Ω| * (3 - 2 * |Ω|) * D ^ 2 + 2 * l * (|Ω| * D) =
        |Ω| / (3 - 2 * |Ω|) * (l + (3 - 2 * |Ω|) * D) ^ 2 := key₂ _ _ hd'
    have h1 : 0 ≤ |Ω| / (3 - 2 * |Ω|) * (l + (3 - 2 * |Ω|) * D) ^ 2 := by positivity
    have h2 : Ω = -|Ω| := by rw [abs_of_nonpos h0, neg_neg]
    rw [← e] at h1
    have h3 : 2 * l * (Ω * D) = -(2 * l * (|Ω| * D)) := by
      nth_rewrite 1 [h2]
      ring
    rw [h3]
    linarith

variable [Fintype ι]

/-- The replacement of Lemma 7 of arXiv 2502.20883.  Lemma 7 bounds `(wᵀ Q φ)²` by
`π φᵀ |Q| M² φ`, which is false for some product rules, see `lemma_7_iff` and
`lemma_7_counterexample`.  The proof of Theorem 3 has room for a larger right-hand side, the weight
`3 |Ω| - 2 Ω²` instead of `|Ω|`, and that weaker estimate holds under `∑ w ψ(Ω) ≤ π` with
`ψ(Ω) = |Ω| / (3 - 2 |Ω|) ≤ |Ω|`. -/
theorem moment_sq_le (w Ω D : ι → ℝ) (hw : ∀ ℓ, 0 ≤ w ℓ) (hΩ : ∀ ℓ, |Ω ℓ| ≤ 1)
    (hp : ∑ ℓ, w ℓ * moderate (Ω ℓ) ≤ π) :
    (∑ ℓ, w ℓ * Ω ℓ * D ℓ) ^ 2 ≤ π * ∑ ℓ, w ℓ * (3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * D ℓ ^ 2 := by
  set m := ∑ ℓ, w ℓ * Ω ℓ * D ℓ with hm
  set Q := ∑ ℓ, w ℓ * (3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * D ℓ ^ 2 with hQ
  have key : ∀ l : ℝ, 2 * l * m ≤ l ^ 2 * π + Q := by
    intro l
    have h1 : ∀ ℓ ∈ (Finset.univ : Finset ι), 2 * l * (w ℓ * Ω ℓ * D ℓ) ≤
        l ^ 2 * (w ℓ * moderate (Ω ℓ)) + w ℓ * (3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * D ℓ ^ 2 := by
      intro ℓ _
      have := mul_le_mul_of_nonneg_left (moderate_mul_add (Ω ℓ) l (D ℓ) (hΩ ℓ)) (hw ℓ)
      nlinarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hm, ← hQ] at h2
    have h3 : l ^ 2 * ∑ ℓ, w ℓ * moderate (Ω ℓ) ≤ l ^ 2 * π := by gcongr
    linarith
  have hπ := Real.pi_pos
  have h := key (m / π)
  have e1 : 2 * (m / π) * m = 2 * (m ^ 2 / π) := by ring
  have e2 : (m / π) ^ 2 * π = m ^ 2 / π := by field_simp
  rw [e1, e2] at h
  have h3 : m ^ 2 / π ≤ Q := by linarith
  rw [div_le_iff₀ hπ] at h3
  linarith

/-- The estimate of one direction that the proof of Theorem 3 needs: the square of the flux
divergence is controlled by the transport term, the increment and the absorption. -/
theorem dir_estimate [Fintype C] [Fintype F] (s : Stencil C F) (w Ω : ι → ℝ)
    (hw : ∀ ℓ, 0 ≤ w ℓ) (hΩ : ∀ ℓ, |Ω ℓ| ≤ 1) (hp : ∑ ℓ, w ℓ * moderate (Ω ℓ) ≤ π)
    {ε c Δt σ₀ : ℝ} (hε : 0 < ε) (hc : 0 < c) (hΔt : 0 < Δt) (hs : 0 < s.Δ) (hσ₀ : 0 ≤ σ₀)
    (hCFL : ∀ ℓ, Ω ℓ ≠ 0 → Δt ≤ 1 / (3 * c) * (ε * s.Δ + σ₀ * s.Δ ^ 2 / (4 * |Ω ℓ|)))
    {g g' : F → ι → ℝ} (hg : ∀ f, ¬ s.IsInner f → ∀ ℓ, g f ℓ = 0)
    (hg' : ∀ f, ¬ s.IsInner f → ∀ ℓ, g' f ℓ = 0) :
    Δt ^ 2 / (2 * π ^ 2) * ∑ z, (∑ ℓ, w ℓ * Ω ℓ * s.D0 (fun f => g' f ℓ) z) ^ 2 ≤
      ε * Δt / (π * c) * ∑ ℓ, w ℓ * ∑ f, g' f ℓ * s.upwind (Ω ℓ) (fun f => g f ℓ) f
      + ε ^ 2 / (4 * π * c ^ 2) * ∑ ℓ, w ℓ * ∑ f, (g f ℓ - g' f ℓ) ^ 2
      + σ₀ * Δt / (2 * π * c) * ∑ ℓ, w ℓ * ∑ f, g' f ℓ ^ 2 := by
  have hπ := Real.pi_pos
  have hΔ := hs.ne'
  set Y : ι → ℝ := fun ℓ => ∑ z, s.D0 (fun f => g' f ℓ) z ^ 2 with hY
  have per : ∀ ℓ, Δt ^ 2 / (2 * π) * ((3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * Y ℓ) ≤
      ε * Δt / (π * c) * ∑ f, g' f ℓ * s.upwind (Ω ℓ) (fun f => g f ℓ) f
      + ε ^ 2 / (4 * π * c ^ 2) * ∑ f, (g f ℓ - g' f ℓ) ^ 2
      + σ₀ * Δt / (2 * π * c) * ∑ f, g' f ℓ ^ 2 := by
    intro ℓ
    set A := ∑ f, g' f ℓ ^ 2 with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun f _ => sq_nonneg _
    have hY0 : 0 ≤ Y ℓ := Finset.sum_nonneg fun f _ => sq_nonneg _
    have hβ : 0 < ε ^ 2 / (4 * π * c ^ 2) := by positivity
    have low := s.upwind_lower hΔ (ε * Δt / (π * c)) hβ (Ω ℓ) (a := fun f => g' f ℓ)
      (b := fun f => g f ℓ) (fun f hf => hg' f hf ℓ) (fun f hf => hg f hf ℓ)
    have cfl : (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * Y ℓ ≤ σ₀ * A := by
      by_cases h0 : Ω ℓ = 0
      · simp only [h0, abs_zero, mul_zero, zero_mul]
        positivity
      by_cases hk : 3 * c * Δt - ε * s.Δ ≤ 0
      · have : (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * Y ℓ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hk (abs_nonneg _)) hY0
        have : 0 ≤ σ₀ * A := by positivity
        linarith
      push Not at hk
      have ht : 0 < |Ω ℓ| := abs_pos.2 h0
      have h8 := s.sum_D0_sq_le hs (a := fun f => g' f ℓ) fun f hf => hg' f hf ℓ
      have h1 := hCFL ℓ h0
      have h2 : (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * (4 / s.Δ ^ 2) ≤ σ₀ := by
        have h3 : 3 * c * Δt ≤ ε * s.Δ + σ₀ * s.Δ ^ 2 / (4 * |Ω ℓ|) := by
          have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 3 * c)
          calc 3 * c * Δt ≤ 3 * c * (1 / (3 * c) * (ε * s.Δ + σ₀ * s.Δ ^ 2 / (4 * |Ω ℓ|))) := this
            _ = _ := by field_simp
        have h4 : 3 * c * Δt - ε * s.Δ ≤ σ₀ * s.Δ ^ 2 / (4 * |Ω ℓ|) := by linarith
        calc (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * (4 / s.Δ ^ 2)
            ≤ σ₀ * s.Δ ^ 2 / (4 * |Ω ℓ|) * |Ω ℓ| * (4 / s.Δ ^ 2) := by gcongr
          _ = σ₀ := by field_simp
      calc (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * Y ℓ
          ≤ (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * (4 / s.Δ ^ 2 * A) := by gcongr
        _ = (3 * c * Δt - ε * s.Δ) * |Ω ℓ| * (4 / s.Δ ^ 2) * A := by ring
        _ ≤ σ₀ * A := by gcongr
    have hmul := mul_le_mul_of_nonneg_left cfl (by positivity : 0 ≤ Δt / (2 * π * c))
    have e1 : Δt / (2 * π * c) * ((3 * c * Δt - ε * s.Δ) * |Ω ℓ| * Y ℓ) =
        Δt ^ 2 / (2 * π) * (3 * |Ω ℓ| * Y ℓ)
          - ε * Δt / (π * c) * (|Ω ℓ| * (s.Δ / 2)) * Y ℓ := by
      field_simp
    have e2 : Δt / (2 * π * c) * (σ₀ * A) = σ₀ * Δt / (2 * π * c) * A := by ring
    have e3 : (ε * Δt / (π * c)) ^ 2 * Ω ℓ ^ 2 / (4 * (ε ^ 2 / (4 * π * c ^ 2))) =
        Δt ^ 2 / π * Ω ℓ ^ 2 := by
      field_simp
    rw [e1, e2] at hmul
    rw [e3] at low
    have e4 : Δt ^ 2 / (2 * π) * ((3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * Y ℓ) =
        Δt ^ 2 / (2 * π) * (3 * |Ω ℓ| * Y ℓ) - Δt ^ 2 / π * Ω ℓ ^ 2 * Y ℓ := by
      field_simp
    rw [e4]
    linarith
  have cs : ∑ z, (∑ ℓ, w ℓ * Ω ℓ * s.D0 (fun f => g' f ℓ) z) ^ 2 ≤
      π * ∑ ℓ, w ℓ * ((3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * Y ℓ) := by
    calc _ ≤ ∑ z, π * ∑ ℓ, w ℓ * (3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * s.D0 (fun f => g' f ℓ) z ^ 2 :=
          Finset.sum_le_sum fun z _ => moment_sq_le w Ω _ hw hΩ hp
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [hY, Finset.mul_sum, mul_assoc]
  calc Δt ^ 2 / (2 * π ^ 2) * ∑ z, (∑ ℓ, w ℓ * Ω ℓ * s.D0 (fun f => g' f ℓ) z) ^ 2
      ≤ Δt ^ 2 / (2 * π ^ 2) * (π * ∑ ℓ, w ℓ * ((3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * Y ℓ)) := by gcongr
    _ = ∑ ℓ, w ℓ * (Δt ^ 2 / (2 * π) * ((3 * |Ω ℓ| - 2 * Ω ℓ ^ 2) * Y ℓ)) := by
        rw [← mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        field_simp
    _ ≤ ∑ ℓ, w ℓ * (ε * Δt / (π * c) * ∑ f, g' f ℓ * s.upwind (Ω ℓ) (fun f => g f ℓ) f
        + ε ^ 2 / (4 * π * c ^ 2) * ∑ f, (g f ℓ - g' f ℓ) ^ 2
        + σ₀ * Δt / (2 * π * c) * ∑ f, g' f ℓ ^ 2) :=
        Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (per ℓ) (hw ℓ)
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ℓ _ => by ring

end Setup

namespace Setup

variable (P : Setup C F ι)

/-- The admissibility of the data: positive constants, and `σ^t ≥ σ₀^t ≥ 0`, `σ^a ≥ 0`. -/
structure IsAdmissible (σ₀ : ℝ) : Prop where
  c_pos : 0 < P.c
  cν_pos : 0 < P.cν
  a_nonneg : 0 ≤ P.a
  Δt_pos : 0 < P.Δt
  Δx_pos : 0 < P.x.Δ
  Δy_pos : 0 < P.y.Δ
  σ₀_nonneg : 0 ≤ σ₀
  σ₀_le : ∀ f, σ₀ ≤ P.σt f
  σa_nonneg : ∀ c, 0 ≤ P.σa c

/-- The CFL condition (3.9) of arXiv 2502.20883.  The paper writes one minimum for all `ℓ` with
`Ω_x^ℓ, Ω_y^ℓ ≠ 0`; each of the two bounds is imposed here for the `ℓ` where its denominator does
not vanish. -/
def CFL (ε σ₀ : ℝ) : Prop :=
  (∀ ℓ, P.Ωx ℓ ≠ 0 → P.Δt ≤ 1 / (3 * P.c) * (ε * P.x.Δ + σ₀ * P.x.Δ ^ 2 / (4 * |P.Ωx ℓ|))) ∧
    ∀ ℓ, P.Ωy ℓ ≠ 0 → P.Δt ≤ 1 / (3 * P.c) * (ε * P.y.Δ + σ₀ * P.y.Δ ^ 2 / (4 * |P.Ωy ℓ|))

variable [Fintype ι]

/-- The properties of the quadrature rule on `P(𝕊²)` that the proof of Theorem 3 uses: nonnegative
weights of total mass `2π`, vanishing first moments (which give `wᵀ g = 0`, an invariant the paper
uses without mention) and points in the unit square. -/
structure IsQuadrature : Prop where
  w_nonneg : ∀ ℓ, 0 ≤ P.w ℓ
  sum_w : ∑ ℓ, P.w ℓ = 2 * π
  sum_Ωx : ∑ ℓ, P.w ℓ * P.Ωx ℓ = 0
  sum_Ωy : ∑ ℓ, P.w ℓ * P.Ωy ℓ = 0
  abs_Ωx_le : ∀ ℓ, |P.Ωx ℓ| ≤ 1
  abs_Ωy_le : ∀ ℓ, |P.Ωy ℓ| ≤ 1

/-- The second moments of the quadrature rule stated in the proof of Theorem 2 of the paper:
`wᵀ Q_x Q_x 𝟙 = wᵀ Q_y Q_y 𝟙 = 2π/3` and `wᵀ Q_x Q_y 𝟙 = 0`. -/
structure IsSecondOrder : Prop where
  sum_ΩxΩx : ∑ ℓ, P.w ℓ * (P.Ωx ℓ * P.Ωx ℓ) = 2 * π / 3
  sum_ΩyΩy : ∑ ℓ, P.w ℓ * (P.Ωy ℓ * P.Ωy ℓ) = 2 * π / 3
  sum_ΩxΩy : ∑ ℓ, P.w ℓ * (P.Ωx ℓ * P.Ωy ℓ) = 0

variable {P}

/-- `ψ(Ω) ≤ |Ω|`, so that the condition of Lemma 7 implies the one of `moment_sq_le`. -/
theorem moderate_le_abs {Ω : ℝ} (hΩ : |Ω| ≤ 1) : moderate Ω ≤ |Ω| :=
  div_le_self (abs_nonneg Ω) (by linarith)

/-- `ψ(Ω) ≤ 1/6 + Ω²`, so that the second moments imply the condition of `moment_sq_le`. -/
theorem moderate_le_sq {Ω : ℝ} (hΩ : |Ω| ≤ 1) : moderate Ω ≤ 1 / 6 + Ω * Ω := by
  have ht : 0 ≤ |Ω| := abs_nonneg Ω
  have hd : 0 < 3 - 2 * |Ω| := by linarith
  rw [moderate, div_le_iff₀ hd, ← abs_mul_abs_self Ω]
  nlinarith [sq_nonneg (|Ω| - 2 / 3), mul_nonneg (mul_nonneg ht ht) (sub_nonneg.2 hΩ)]

/-- The condition of `moment_sq_le` follows from the second moments of the rule. -/
theorem sum_moderate_le (w Ω : ι → ℝ) (hw : ∀ ℓ, 0 ≤ w ℓ) (hΩ : ∀ ℓ, |Ω ℓ| ≤ 1)
    (h1 : ∑ ℓ, w ℓ = 2 * π) (h2 : ∑ ℓ, w ℓ * (Ω ℓ * Ω ℓ) = 2 * π / 3) :
    ∑ ℓ, w ℓ * moderate (Ω ℓ) ≤ π := by
  calc ∑ ℓ, w ℓ * moderate (Ω ℓ) ≤ ∑ ℓ, (1 / 6 * w ℓ + w ℓ * (Ω ℓ * Ω ℓ)) :=
        Finset.sum_le_sum fun ℓ _ => by
          have := mul_le_mul_of_nonneg_left (moderate_le_sq (hΩ ℓ)) (hw ℓ)
          linarith
    _ = π := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
        ring

/-- `wᵀ (I - (1/2π) 𝟙 wᵀ) = 0`. -/
theorem sum_w_meanFree (h : ∑ ℓ, P.w ℓ = 2 * π) (v : ι → ℝ) :
    ∑ ℓ, P.w ℓ * P.meanFree v ℓ = 0 := by
  have hπ := Real.pi_ne_zero
  simp only [meanFree, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h]
  field_simp
  ring


end Setup

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- The invariant `⟨g⟩ = wᵀ g = 0` that the proof of Theorem 3 of arXiv 2502.20883 uses for
`g^{n+1}`: it propagates through (3.3a). -/
theorem sum_w_step {σ₀ ε : ℝ} (hQ : P.IsQuadrature) (hA : P.IsAdmissible σ₀) (hε : 0 < ε)
    {g g' : F → ι → ℝ} {h T h' T' : C → ℝ} (hs : P.IsStep ε g h T g' h' T')
    (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g f ℓ = 0) (f : F) : ∑ ℓ, P.w ℓ * g' f ℓ = 0 := by
  by_cases hf : P.Inner f
  · have hc := hA.c_pos
    have hΔt := hA.Δt_pos
    have hκ : 0 < ε ^ 2 / (P.c * P.Δt) := by positivity
    have hσ : 0 ≤ P.σt f := hA.σ₀_nonneg.trans (hA.σ₀_le f)
    have e : ∑ ℓ, P.w ℓ * (ε ^ 2 / (P.c * P.Δt) * (g' f ℓ - g f ℓ)
        + ε * P.meanFree (P.transport g f) ℓ + P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        + P.Ωy ℓ * P.y.δ (P.phi ε h T) f) = ∑ ℓ, P.w ℓ * (-P.σt f * g' f ℓ) :=
      Finset.sum_congr rfl fun ℓ _ => by
        have := hs.g_eq f hf ℓ
        rw [MicroEq] at this
        rw [this]
    have e1 : ∀ ℓ, P.w ℓ * (ε ^ 2 / (P.c * P.Δt) * (g' f ℓ - g f ℓ)
        + ε * P.meanFree (P.transport g f) ℓ + P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        + P.Ωy ℓ * P.y.δ (P.phi ε h T) f) =
        ε ^ 2 / (P.c * P.Δt) * (P.w ℓ * g' f ℓ) - ε ^ 2 / (P.c * P.Δt) * (P.w ℓ * g f ℓ)
        + ε * (P.w ℓ * P.meanFree (P.transport g f) ℓ) + P.w ℓ * P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        + P.w ℓ * P.Ωy ℓ * P.y.δ (P.phi ε h T) f := fun ℓ => by ring
    have e2 : ∀ ℓ, P.w ℓ * (-P.σt f * g' f ℓ) = -P.σt f * (P.w ℓ * g' f ℓ) := fun ℓ => by ring
    simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hg0, hQ.sum_Ωx, hQ.sum_Ωy, sum_w_meanFree hQ.sum_w] at e
    have e3 : (ε ^ 2 / (P.c * P.Δt) + P.σt f) * ∑ ℓ, P.w ℓ * g' f ℓ = 0 := by linarith
    exact (mul_eq_zero.1 e3).resolve_left (by positivity)
  · simp [hs.wall f hf]

/-- The face-wise energy identity: (3.3a) tested with `g'ᵀ M²`, using `wᵀ g' = 0`. -/
theorem micro_face {ε : ℝ} {g g' : F → ι → ℝ} {h T h' T' : C → ℝ}
    (hs : P.IsStep ε g h T g' h' T') (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g' f ℓ = 0) (f : F) :
    ε ^ 2 / (P.c * P.Δt) * ∑ ℓ, P.w ℓ * (g' f ℓ * (g' f ℓ - g f ℓ))
      + ε * (∑ ℓ, P.w ℓ * (g' f ℓ * P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f)
        + ∑ ℓ, P.w ℓ * (g' f ℓ * P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f))
      + (∑ ℓ, P.w ℓ * P.Ωx ℓ * g' f ℓ) * P.x.δ (P.phi ε h T) f
      + (∑ ℓ, P.w ℓ * P.Ωy ℓ * g' f ℓ) * P.y.δ (P.phi ε h T) f =
      -P.σt f * ∑ ℓ, P.w ℓ * g' f ℓ ^ 2 := by
  by_cases hf : P.Inner f
  · have hMF : ∑ ℓ, P.w ℓ * (g' f ℓ * P.meanFree (P.transport g f) ℓ) =
        ∑ ℓ, P.w ℓ * (g' f ℓ * P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f)
        + ∑ ℓ, P.w ℓ * (g' f ℓ * P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f) := by
      have e : ∀ ℓ, P.w ℓ * (g' f ℓ * P.meanFree (P.transport g f) ℓ) =
          P.w ℓ * (g' f ℓ * P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f)
          + P.w ℓ * (g' f ℓ * P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f)
          - (1 / (2 * π) * ∑ ℓ', P.w ℓ' * P.transport g f ℓ') * (P.w ℓ * g' f ℓ) := fun ℓ => by
        simp only [meanFree]
        simp only [transport]
        ring
      simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hg0 f]
      ring
    have e : ∑ ℓ, P.w ℓ * (g' f ℓ * (ε ^ 2 / (P.c * P.Δt) * (g' f ℓ - g f ℓ)
        + ε * P.meanFree (P.transport g f) ℓ + P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        + P.Ωy ℓ * P.y.δ (P.phi ε h T) f)) = ∑ ℓ, P.w ℓ * (g' f ℓ * (-P.σt f * g' f ℓ)) :=
      Finset.sum_congr rfl fun ℓ _ => by
        have := hs.g_eq f hf ℓ
        rw [MicroEq] at this
        rw [this]
    have e1 : ∀ ℓ, P.w ℓ * (g' f ℓ * (ε ^ 2 / (P.c * P.Δt) * (g' f ℓ - g f ℓ)
        + ε * P.meanFree (P.transport g f) ℓ + P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        + P.Ωy ℓ * P.y.δ (P.phi ε h T) f)) =
        ε ^ 2 / (P.c * P.Δt) * (P.w ℓ * (g' f ℓ * (g' f ℓ - g f ℓ)))
        + ε * (P.w ℓ * (g' f ℓ * P.meanFree (P.transport g f) ℓ))
        + P.w ℓ * P.Ωx ℓ * g' f ℓ * P.x.δ (P.phi ε h T) f
        + P.w ℓ * P.Ωy ℓ * g' f ℓ * P.y.δ (P.phi ε h T) f := fun ℓ => by ring
    have e2 : ∀ ℓ, P.w ℓ * (g' f ℓ * (-P.σt f * g' f ℓ)) = -P.σt f * (P.w ℓ * g' f ℓ ^ 2) :=
      fun ℓ => by ring
    simp only [e1, e2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hMF] at e
    exact e
  · simp [hs.wall f hf]

/-- The discrete energy is the paper's (3.8), written through the normalized quantities used in the
proof.  This is where `T ≥ 0` gives `(T^{5/2})² = T⁵`. -/
theorem energy_eq [Fintype C] [Fintype F] {ε : ℝ} (g : F → ι → ℝ) (h : C → ℝ) {T : C → ℝ}
    (ha : 0 ≤ P.a * P.cν) (hT : ∀ z, 0 ≤ T z) :
    P.energy ε g h T = P.Δζ * (∑ z, (P.phi ε h T z / P.c) ^ 2
      + ε ^ 2 / (2 * π * P.c ^ 2) * ∑ ℓ, P.w ℓ * ∑ f, g f ℓ ^ 2
      + 2 / 5 * (P.a * P.cν / (2 * π) ^ 2) * ∑ z, T z ^ 5) := by
  have e3 : ∀ z, (√(P.a * P.cν) / (2 * π) * T z ^ (5 / 2 : ℝ)) ^ 2 * P.Δζ =
      P.Δζ * (P.a * P.cν / (2 * π) ^ 2 * T z ^ 5) := fun z => by
    have : (T z ^ (5 / 2 : ℝ)) ^ 2 = T z ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hT z), ← Real.rpow_natCast]
      norm_num
    rw [mul_pow, div_pow, Real.sq_sqrt ha, this]
    ring
  have e1 : ∑ z, (1 / P.c * P.B (T z) + ε ^ 2 / P.c * h z) ^ 2 * P.Δζ =
      P.Δζ * ∑ z, (P.phi ε h T z / P.c) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by simp only [phi]; ring
  have e2 : 1 / (2 * π) * ∑ f, ∑ ℓ, P.w ℓ * (ε / P.c * g f ℓ) ^ 2 * P.Δζ =
      P.Δζ * (ε ^ 2 / (2 * π * P.c ^ 2) * ∑ ℓ, P.w ℓ * ∑ f, g f ℓ ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun f _ => by
      field_simp
  rw [energy, e1, e2]
  simp only [e3, ← Finset.mul_sum]
  ring

end Setup

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- The cell-wise bound of the thermal energy: Lemma 9 applied to (3.3c) (the step from (A.20) on in
arXiv 2502.20883). -/
theorem thermal_cell {σ₀ : ℝ} (hA : P.IsAdmissible σ₀) {ε : ℝ} {h T h' T' : C → ℝ}
    {g' : F → ι → ℝ} (hs : P.IsMacroStep ε h T g' h' T') {z : C} (hT : 0 ≤ T z) (hT' : 0 ≤ T' z) :
    2 / 5 * (P.a * P.cν / (2 * π) ^ 2) * (T' z ^ 5 - T z ^ 5) ≤
      2 * (P.Δt * (P.σa z * h' z * (P.B (T' z) / P.c))) := by
  have hπ := Real.pi_pos
  have hc := hA.c_pos
  have hcν := hA.cν_pos
  have hΔt := hA.Δt_pos
  have h9 := lemma_9 hT' hT
  have e := hs.T_eq z
  have e' : P.cν * (T' z - T z) = 2 * π * P.Δt * P.σa z * h' z := by
    field_simp at e
    linear_combination e
  have hnn : 0 ≤ 2 * (P.a * P.cν / (2 * π) ^ 2) := by
    have := hA.a_nonneg
    positivity
  have hmul := mul_le_mul_of_nonneg_left (show 1 / 5 * (T' z ^ 5 - T z ^ 5) ≤
    T' z ^ 4 * (T' z - T z) by linarith) hnn
  have e2 : 2 * (P.Δt * (P.σa z * h' z * (P.B (T' z) / P.c))) =
      2 * (P.a / (2 * π) ^ 2) * T' z ^ 4 * (2 * π * P.Δt * P.σa z * h' z) := by
    simp only [B]
    field_simp
  rw [e2, ← e']
  calc 2 / 5 * (P.a * P.cν / (2 * π) ^ 2) * (T' z ^ 5 - T z ^ 5)
      = 2 * (P.a * P.cν / (2 * π) ^ 2) * (1 / 5 * (T' z ^ 5 - T z ^ 5)) := by ring
    _ ≤ _ := hmul
    _ = _ := by ring

/-- The energy estimate behind **Theorem 3 of arXiv 2502.20883**, under the quadrature condition
`∑ w ψ(Ω) ≤ π` of `moment_sq_le`.  The argument follows Appendix A of the paper except at two
places: the transport term is bounded per quadrature direction with `Ω² ≤ |Ω|` left in place, and
Lemma 7 is replaced by `moment_sq_le`.  The hypotheses `hT`, `hT'` are the positivity of Lemma 9,
which is not implied by the scheme. -/
theorem energy_le_of_moderate [Fintype C] [Fintype F] {σ₀ ε : ℝ} (hQ : P.IsQuadrature)
    (hA : P.IsAdmissible σ₀) (hε : 0 < ε) (hCFL : P.CFL ε σ₀)
    (hpx : ∑ ℓ, P.w ℓ * moderate (P.Ωx ℓ) ≤ π) (hpy : ∑ ℓ, P.w ℓ * moderate (P.Ωy ℓ) ≤ π)
    {g g' : F → ι → ℝ} {h T h' T' : C → ℝ} (hs : P.IsStep ε g h T g' h' T')
    (hgw : ∀ f, ¬ P.Inner f → ∀ ℓ, g f ℓ = 0) (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g f ℓ = 0)
    (hT : ∀ z, 0 ≤ T z) (hT' : ∀ z, 0 ≤ T' z) :
    P.energy ε g' h' T' ≤ P.energy ε g h T := by
  have hπ := Real.pi_pos
  have hc := hA.c_pos
  have hcν := hA.cν_pos
  have hΔt := hA.Δt_pos
  have hσ₀ := hA.σ₀_nonneg
  have ha : 0 ≤ P.a * P.cν := mul_nonneg hA.a_nonneg hcν.le
  have hg0' := sum_w_step hQ hA hε hs hg0
  have hwx : ∀ f, ¬ P.x.IsInner f → ∀ ℓ, g' f ℓ = 0 := fun f hf => hs.wall f fun h => hf h.1
  have hwy : ∀ f, ¬ P.y.IsInner f → ∀ ℓ, g' f ℓ = 0 := fun f hf => hs.wall f fun h => hf h.2
  rw [energy_eq g' h' ha hT', energy_eq g h ha hT]
  refine mul_le_mul_of_nonneg_left ?_ (mul_pos hA.Δx_pos hA.Δy_pos).le
  set φ := P.phi ε h T with hφ
  set φ' := P.phi ε h' T' with hφ'
  set mx := P.wQD P.x P.Ωx g' with hmx
  set my := P.wQD P.y P.Ωy g' with hmy
  set Pn := ∑ z, (φ z / P.c) ^ 2 with hPn
  set Pn' := ∑ z, (φ' z / P.c) ^ 2 with hPn'
  set R := ∑ z, (φ' z / P.c - φ z / P.c) ^ 2 with hR
  set Gn := ∑ ℓ, P.w ℓ * ∑ f, g f ℓ ^ 2 with hGn
  set Gn' := ∑ ℓ, P.w ℓ * ∑ f, g' f ℓ ^ 2 with hGn'
  set Dg := ∑ ℓ, P.w ℓ * ∑ f, (g f ℓ - g' f ℓ) ^ 2 with hDg
  set Ux := ∑ ℓ, P.w ℓ * ∑ f, g' f ℓ * P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f with hUx
  set Uy := ∑ ℓ, P.w ℓ * ∑ f, g' f ℓ * P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f with hUy
  set Hφ := ∑ z, P.σa z * h' z * (φ' z / P.c) with hHφ
  set HB := ∑ z, P.σa z * h' z * (P.B (T' z) / P.c) with hHB
  set Sxφ := ∑ z, mx z * φ z with hSxφ
  set Syφ := ∑ z, my z * φ z with hSyφ
  set Sxφ' := ∑ z, mx z * (φ' z / P.c) with hSxφ'
  set Syφ' := ∑ z, my z * (φ' z / P.c) with hSyφ'
  set Sxx := ∑ z, mx z ^ 2 with hSxx
  set Syy := ∑ z, my z ^ 2 with hSyy
  set Wn := ∑ z, T z ^ 5 with hWn
  set Wn' := ∑ z, T' z ^ 5 with hWn'
  set ka := ε ^ 2 / (2 * π * P.c ^ 2) with hka
  set kb := ε * P.Δt / (π * P.c) with hkb
  set kc := P.Δt / π with hkc
  set kd := σ₀ * P.Δt / (π * P.c) with hkd
  set ke := P.Δt ^ 2 / (2 * π ^ 2) with hke
  set kf := P.Δt / (π * P.c) with hkf
  set kth := 2 / 5 * (P.a * P.cν / (2 * π) ^ 2) with hkth
  have hHe : 0 ≤ P.Δt * (ε ^ 2 / P.c * ∑ z, P.σa z * h' z ^ 2) := by
    have : 0 ≤ ∑ z, P.σa z * h' z ^ 2 :=
      Finset.sum_nonneg fun z _ => mul_nonneg (hA.σa_nonneg z) (sq_nonneg _)
    positivity
  -- the macro identity
  have hmacro : Pn' - Pn + R + 2 * (P.Δt * Hφ) + kc * Sxφ' + kc * Syφ' = 0 := by
    have hcell : ∀ z, (φ' z / P.c) ^ 2 - (φ z / P.c) ^ 2 + (φ' z / P.c - φ z / P.c) ^ 2
        + 2 * (P.Δt * (P.σa z * h' z * (φ' z / P.c))) + kc * (mx z * (φ' z / P.c))
        + kc * (my z * (φ' z / P.c)) = 0 := fun z => by
      have e := (theorem_1 hs.toIsMacroStep z).1
      have huv : φ' z / P.c - φ z / P.c = -P.Δt * P.σa z * h' z
          - P.Δt / (2 * π) * (mx z + my z) := by
        simp only [hφ, hφ', hmx, hmy]
        field_simp at e ⊢
        linear_combination e
      have : kc = 2 * (P.Δt / (2 * π)) := by
        rw [hkc]
        field_simp
      rw [this]
      linear_combination (2 * (φ' z / P.c)) * huv
    have := Finset.sum_congr (rfl : (Finset.univ : Finset C) = Finset.univ) fun z _ => hcell z
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const_zero] at this
    exact this
  -- the micro identity
  have hmicro : ka * (Gn' - Gn + Dg) + kb * (Ux + Uy) - kf * (Sxφ + Syφ) ≤ -kd * Gn' := by
    have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset F) = Finset.univ)
      fun f _ => micro_face hs hg0' f
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have c1 : ∑ f, ∑ ℓ, P.w ℓ * (g' f ℓ * (g' f ℓ - g f ℓ)) = 1 / 2 * (Gn' - Gn + Dg) := by
      rw [Finset.sum_comm, hGn, hGn', hDg]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun f _ => by ring
    have c2x : ∑ f, ∑ ℓ, P.w ℓ * (g' f ℓ * P.x.upwind (P.Ωx ℓ) (fun f => g f ℓ) f) = Ux := by
      rw [Finset.sum_comm, hUx]
      simp only [Finset.mul_sum]
    have c2y : ∑ f, ∑ ℓ, P.w ℓ * (g' f ℓ * P.y.upwind (P.Ωy ℓ) (fun f => g f ℓ) f) = Uy := by
      rw [Finset.sum_comm, hUy]
      simp only [Finset.mul_sum]
    have c3x : ∑ f, (∑ ℓ, P.w ℓ * P.Ωx ℓ * g' f ℓ) * P.x.δ φ f = -Sxφ := by
      rw [P.x.sum_mul_δ φ fun f hf => by simp [hwx f hf]]
      simp only [hSxφ, hmx, wQD_eq_D0]
    have c3y : ∑ f, (∑ ℓ, P.w ℓ * P.Ωy ℓ * g' f ℓ) * P.y.δ φ f = -Syφ := by
      rw [P.y.sum_mul_δ φ fun f hf => by simp [hwy f hf]]
      simp only [hSyφ, hmy, wQD_eq_D0]
    have c4 : σ₀ * Gn' ≤ ∑ f, P.σt f * ∑ ℓ, P.w ℓ * g' f ℓ ^ 2 := by
      have e : Gn' = ∑ f, ∑ ℓ, P.w ℓ * g' f ℓ ^ 2 := by
        rw [Finset.sum_comm, hGn']
        simp only [Finset.mul_sum]
      rw [e, Finset.mul_sum]
      refine Finset.sum_le_sum fun f _ => ?_
      exact mul_le_mul_of_nonneg_right (hA.σ₀_le f) (Finset.sum_nonneg fun ℓ _ =>
        mul_nonneg (hQ.w_nonneg ℓ) (sq_nonneg _))
    have hsum' : ε ^ 2 / (P.c * P.Δt) * (1 / 2 * (Gn' - Gn + Dg)) + ε * (Ux + Uy) - Sxφ - Syφ ≤
        -σ₀ * Gn' := by
      have e : ∑ f, -P.σt f * ∑ ℓ, P.w ℓ * g' f ℓ ^ 2 =
          -∑ f, P.σt f * ∑ ℓ, P.w ℓ * g' f ℓ ^ 2 := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun f _ => by ring
      rw [c1, c2x, c2y, c3x, c3y, e] at hsum
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum' (by positivity : 0 ≤ kf)
    have e1 : kf * (ε ^ 2 / (P.c * P.Δt) * (1 / 2 * (Gn' - Gn + Dg)) + ε * (Ux + Uy) - Sxφ - Syφ) =
        ka * (Gn' - Gn + Dg) + kb * (Ux + Uy) - kf * (Sxφ + Syφ) := by
      rw [hkf, hka, hkb]
      field_simp
      ring
    have e2 : kf * (-σ₀ * Gn') = -kd * Gn' := by
      rw [hkf, hkd]
      ring
    rwa [e1, e2] at hmul
  -- the cross terms
  have hcross : ∀ m : C → ℝ, 0 ≤ kc * ∑ z, m z * (φ' z / P.c) - kf * ∑ z, m z * φ z
      + 1 / 2 * R + ke * ∑ z, m z ^ 2 := by
    intro m
    have hterm : ∀ z, 0 ≤ kc * (m z * (φ' z / P.c)) - kf * (m z * φ z)
        + 1 / 2 * (φ' z / P.c - φ z / P.c) ^ 2 + ke * m z ^ 2 := fun z => by
      have e : kc * (m z * (φ' z / P.c)) - kf * (m z * φ z)
          + 1 / 2 * (φ' z / P.c - φ z / P.c) ^ 2 + ke * m z ^ 2 =
          1 / 2 * ((φ' z / P.c - φ z / P.c) + kc * m z) ^ 2 := by
        rw [hkc, hkf, hke]
        field_simp
        ring
      rw [e]
      positivity
    have := Finset.sum_nonneg fun z (_ : z ∈ (Finset.univ : Finset C)) => hterm z
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using this
  have hcx := hcross mx
  have hcy := hcross my
  -- the two directions
  have e1 : ε ^ 2 / (4 * π * P.c ^ 2) = ka / 2 := by
    rw [hka]
    field_simp
    ring
  have e2 : σ₀ * P.Δt / (2 * π * P.c) = kd / 2 := by
    rw [hkd]
    field_simp
  have hdx : ke * Sxx ≤ kb * Ux + ka / 2 * Dg + kd / 2 * Gn' := by
    have := dir_estimate P.x P.w P.Ωx hQ.w_nonneg hQ.abs_Ωx_le hpx hε hc hΔt hA.Δx_pos hσ₀ hCFL.1
      (g := g) (g' := g') (fun f hf => hgw f fun h => hf h.1) hwx
    rw [e1, e2] at this
    exact this
  have hdy : ke * Syy ≤ kb * Uy + ka / 2 * Dg + kd / 2 * Gn' := by
    have := dir_estimate P.y P.w P.Ωy hQ.w_nonneg hQ.abs_Ωy_le hpy hε hc hΔt hA.Δy_pos hσ₀ hCFL.2
      (g := g) (g' := g') (fun f hf => hgw f fun h => hf h.2) hwy
    rw [e1, e2] at this
    exact this
  -- the thermal part
  have hth : kth * (Wn' - Wn) ≤ 2 * (P.Δt * HB) := by
    have := Finset.sum_le_sum fun z (_ : z ∈ (Finset.univ : Finset C)) =>
      thermal_cell hA hs.toIsMacroStep (hT z) (hT' z)
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at this
    exact this
  have hsplit : P.Δt * Hφ = P.Δt * HB + P.Δt * (ε ^ 2 / P.c * ∑ z, P.σa z * h' z ^ 2) := by
    have e : Hφ = HB + ε ^ 2 / P.c * ∑ z, P.σa z * h' z ^ 2 := by
      rw [hHφ, hHB, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hφ', phi]
      ring
    rw [e]
    ring
  linarith

end Setup

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- **Theorem 3 of arXiv 2502.20883** (nonlinear energy stability) of the full-rank scheme (3.3),
with the constants of the paper: `e^{n+1} ≤ eⁿ` under the CFL condition (3.9).  It holds for zero
and for periodic boundary conditions (`hgw` is empty on a periodic grid).  Differences from the
paper: the hypotheses left implicit there are stated (`hQ`, `hQ2`, `hA`, `⟨gⁿ⟩ = 0`, and the
positivity `T, T' ≥ 0` of Lemma 9, without which `T^{5/2}` is not even defined); `⟨g^{n+1}⟩ = 0` is
derived (`sum_w_step`); and the proof does not use Lemma 7, which is false for some product rules
(`lemma_7_counterexample`), but `moment_sq_le`, whose quadrature condition follows from the second
moments. -/
theorem theorem_3 [Fintype C] [Fintype F] {σ₀ ε : ℝ} (hQ : P.IsQuadrature)
    (hQ2 : P.IsSecondOrder) (hA : P.IsAdmissible σ₀) (hε : 0 < ε) (hCFL : P.CFL ε σ₀)
    {g g' : F → ι → ℝ} {h T h' T' : C → ℝ} (hs : P.IsStep ε g h T g' h' T')
    (hgw : ∀ f, ¬ P.Inner f → ∀ ℓ, g f ℓ = 0) (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g f ℓ = 0)
    (hT : ∀ z, 0 ≤ T z) (hT' : ∀ z, 0 ≤ T' z) :
    P.energy ε g' h' T' ≤ P.energy ε g h T :=
  energy_le_of_moderate hQ hA hε hCFL
    (sum_moderate_le _ _ hQ.w_nonneg hQ.abs_Ωx_le hQ.sum_w hQ2.sum_ΩxΩx)
    (sum_moderate_le _ _ hQ.w_nonneg hQ.abs_Ωy_le hQ.sum_w hQ2.sum_ΩyΩy) hs hgw hg0 hT hT'

/-- **Theorem 3 of arXiv 2502.20883** without the second moments, under the condition
`∑ w |Ω_v| ≤ π` that is equivalent to Lemma 7 of the paper (`lemma_7_iff`). -/
theorem theorem_3_of_lemma_7 [Fintype C] [Fintype F] {σ₀ ε : ℝ} (hQ : P.IsQuadrature)
    (hx : ∑ ℓ, P.w ℓ * |P.Ωx ℓ| ≤ π) (hy : ∑ ℓ, P.w ℓ * |P.Ωy ℓ| ≤ π)
    (hA : P.IsAdmissible σ₀) (hε : 0 < ε) (hCFL : P.CFL ε σ₀)
    {g g' : F → ι → ℝ} {h T h' T' : C → ℝ} (hs : P.IsStep ε g h T g' h' T')
    (hgw : ∀ f, ¬ P.Inner f → ∀ ℓ, g f ℓ = 0) (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g f ℓ = 0)
    (hT : ∀ z, 0 ≤ T z) (hT' : ∀ z, 0 ≤ T' z) :
    P.energy ε g' h' T' ≤ P.energy ε g h T :=
  energy_le_of_moderate hQ hA hε hCFL
    ((Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (moderate_le_abs (hQ.abs_Ωx_le ℓ))
      (hQ.w_nonneg ℓ)).trans hx)
    ((Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (moderate_le_abs (hQ.abs_Ωy_le ℓ))
      (hQ.w_nonneg ℓ)).trans hy) hs hgw hg0 hT hT'

/-- **Theorem 3 of arXiv 2502.20883** along a whole trajectory: the energy is nonincreasing.  The
invariant `⟨gⁿ⟩ = 0` is only needed at `n = 0`. -/
theorem theorem_3_antitone [Fintype C] [Fintype F] {σ₀ ε : ℝ} (hQ : P.IsQuadrature)
    (hQ2 : P.IsSecondOrder) (hA : P.IsAdmissible σ₀) (hε : 0 < ε) (hCFL : P.CFL ε σ₀)
    {g : ℕ → F → ι → ℝ} {h T : ℕ → C → ℝ}
    (hs : ∀ n, P.IsStep ε (g n) (h n) (T n) (g (n + 1)) (h (n + 1)) (T (n + 1)))
    (hgw : ∀ f, ¬ P.Inner f → ∀ ℓ, g 0 f ℓ = 0) (hg0 : ∀ f, ∑ ℓ, P.w ℓ * g 0 f ℓ = 0)
    (hT : ∀ n z, 0 ≤ T n z) : Antitone fun n => P.energy ε (g n) (h n) (T n) := by
  have hm : ∀ n f, ∑ ℓ, P.w ℓ * g n f ℓ = 0 := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => exact sum_w_step hQ hA hε (hs n) ih
  refine antitone_nat_of_succ_le fun n => ?_
  refine theorem_3 hQ hQ2 hA hε hCFL (hs n) ?_ (hm n) (hT n) (hT (n + 1))
  cases n with
  | zero => exact hgw
  | succ n => exact (hs n).wall

end Setup

/-- **Lemma 7 of arXiv 2502.20883** for a given rule is *equivalent* to `∑ w |Ω| ≤ π`.  The paper
states Lemma 7 without proof.  The integral `∫ |Ω_x| dΩ` over `P(𝕊²)` is `π`, but a quadrature need
not satisfy `∑ w |Ω| ≤ π`, see `lemma_7_counterexample`. -/
theorem lemma_7_iff [Fintype ι] (w Ω : ι → ℝ) (hw : ∀ ℓ, 0 ≤ w ℓ) :
    (∀ φ : ι → ℝ, (∑ ℓ, Ω ℓ * φ ℓ * w ℓ) ^ 2 ≤ π * ∑ ℓ, φ ℓ * |Ω ℓ| * w ℓ * φ ℓ) ↔
      ∑ ℓ, w ℓ * |Ω ℓ| ≤ π := by
  have hπ := Real.pi_pos
  have hS : 0 ≤ ∑ ℓ, w ℓ * |Ω ℓ| := Finset.sum_nonneg fun ℓ _ => mul_nonneg (hw ℓ) (abs_nonneg _)
  constructor
  · intro h
    have h1 := h fun ℓ => if 0 ≤ Ω ℓ then 1 else -1
    have e1 : ∑ ℓ, Ω ℓ * (if 0 ≤ Ω ℓ then 1 else -1) * w ℓ = ∑ ℓ, w ℓ * |Ω ℓ| :=
      Finset.sum_congr rfl fun ℓ _ => by
        split_ifs with h0
        · rw [abs_of_nonneg h0]; ring
        · rw [abs_of_neg (not_le.1 h0)]; ring
    have e2 : ∑ ℓ, (if 0 ≤ Ω ℓ then 1 else -1) * |Ω ℓ| * w ℓ * (if 0 ≤ Ω ℓ then 1 else -1) =
        ∑ ℓ, w ℓ * |Ω ℓ| :=
      Finset.sum_congr rfl fun ℓ _ => by split_ifs <;> ring
    rw [e1, e2] at h1
    by_contra hc
    push Not at hc
    have : π * ∑ ℓ, w ℓ * |Ω ℓ| < (∑ ℓ, w ℓ * |Ω ℓ|) ^ 2 := by nlinarith
    linarith
  · intro h φ
    have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
      (r := fun ℓ => Ω ℓ * φ ℓ * w ℓ) (f := fun ℓ => w ℓ * |Ω ℓ|)
      (g := fun ℓ => φ ℓ * |Ω ℓ| * w ℓ * φ ℓ)
      (fun ℓ _ => mul_nonneg (hw ℓ) (abs_nonneg _))
      (fun ℓ _ => by
        have := mul_nonneg (mul_nonneg (abs_nonneg (Ω ℓ)) (hw ℓ)) (sq_nonneg (φ ℓ))
        nlinarith)
      (fun ℓ _ => le_of_eq (by
        have := sq_abs (Ω ℓ)
        have e : (Ω ℓ * φ ℓ * w ℓ) ^ 2 = |Ω ℓ| ^ 2 * φ ℓ ^ 2 * w ℓ ^ 2 := by rw [this]; ring
        rw [e]
        ring))
    have hg : 0 ≤ ∑ ℓ, φ ℓ * |Ω ℓ| * w ℓ * φ ℓ := Finset.sum_nonneg fun ℓ _ => by
      have := mul_nonneg (mul_nonneg (abs_nonneg (Ω ℓ)) (hw ℓ)) (sq_nonneg (φ ℓ))
      nlinarith
    exact cs.trans (mul_le_mul_of_nonneg_right h hg)

/-- The weights of the order-two product rule on `P(𝕊²)`. -/
def s2w (_ : Bool × Bool) : ℝ := π / 2

/-- The first components of the points of the order-two product rule, `±1/√3`. -/
def s2x (b : Bool × Bool) : ℝ := (if b.1 then 1 else -1) / √3

/-- The second components of the points of the order-two product rule, `±1/√3`. -/
def s2y (b : Bool × Bool) : ℝ := (if b.2 then 1 else -1) / √3

/-- `√3 √3 = 3`. -/
theorem s2_sqrt : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- The moments of the order-two product rule are those required by the paper. -/
theorem s2_moments :
    ∑ b, s2w b = 2 * π ∧ ∑ b, s2w b * s2x b = 0 ∧ ∑ b, s2w b * s2y b = 0 ∧
      ∑ b, s2w b * (s2x b * s2x b) = 2 * π / 3 ∧ ∑ b, s2w b * (s2y b * s2y b) = 2 * π / 3 ∧
      ∑ b, s2w b * (s2x b * s2y b) = 0 := by
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  have h := s2_sqrt
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, s2w, s2x, s2y, ite_true, ite_false,
    Bool.false_eq_true]
  refine ⟨by ring, by ring, by ring, ?_, ?_, by ring⟩ <;> field_simp <;> nlinarith [h]

/-- **Lemma 7 of arXiv 2502.20883 is false for a product rule.**  The rule with the four points
`(±1/√3, ±1/√3)` and weights `π/2` is the tensorized Gauss–Legendre rule of order two on `P(𝕊²)`
(two Gauss points `μ = ±1/√3`, four azimuthal midpoints); it has all the moments the paper asks for
(`s2_moments`), but `∑ w |Ω_x| = 2π/√3 > π`.  Theorem 3 is not affected: see `theorem_3`. -/
theorem lemma_7_counterexample :
    ¬ ∀ φ : Bool × Bool → ℝ,
      (∑ ℓ, s2x ℓ * φ ℓ * s2w ℓ) ^ 2 ≤ π * ∑ ℓ, φ ℓ * |s2x ℓ| * s2w ℓ * φ ℓ := by
  rw [lemma_7_iff _ _ fun _ => by simp only [s2w]; positivity]
  have hπ := Real.pi_pos
  have h3 : (0 : ℝ) < √3 := by positivity
  have hlt : √3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have e : ∑ b, s2w b * |s2x b| = 2 * π / √3 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, s2w, s2x, ite_true, ite_false,
      Bool.false_eq_true, abs_div, abs_one, abs_neg, abs_of_pos h3]
    field_simp
    ring
  rw [e, not_le, lt_div_iff₀ h3]
  nlinarith

/-! ### The periodic staggered grid -/

/-- The cell nodes and the faces of the periodic staggered grid.  As a cell node, `(false, i, j)` is
the centre `(x_i, y_j)` and `(true, i, j)` the corner `(x_{i+½}, y_{j+½})`.  As a face,
`(false, i, j)` is `(x_{i+½}, y_j)` and `(true, i, j)` is `(x_i, y_{j+½})`. -/
abbrev Node (Nx Ny : ℕ) := Bool × ZMod Nx × ZMod Ny

/-- The `x` direction of the periodic staggered grid. -/
def periodicX (Nx Ny : ℕ) (Δx : ℝ) : Stencil (Node Nx Ny) (Node Nx Ny) where
  right c := (c.1, if c.1 then c.2.1 + 1 else c.2.1, c.2.2)
  left c := (c.1, if c.1 then c.2.1 else c.2.1 - 1, c.2.2)
  ahead f := (f.1, if f.1 then f.2.1 else f.2.1 + 1, f.2.2)
  behind f := (f.1, if f.1 then f.2.1 - 1 else f.2.1, f.2.2)
  ahead_left c := by rcases c with ⟨b, i, j⟩; cases b <;> simp
  behind_right c := by rcases c with ⟨b, i, j⟩; cases b <;> simp
  Δ := Δx

/-- The `y` direction of the periodic staggered grid. -/
def periodicY (Nx Ny : ℕ) (Δy : ℝ) : Stencil (Node Nx Ny) (Node Nx Ny) where
  right c := (!c.1, c.2.1, if c.1 then c.2.2 + 1 else c.2.2)
  left c := (!c.1, c.2.1, if c.1 then c.2.2 else c.2.2 - 1)
  ahead f := (!f.1, f.2.1, if f.1 then f.2.2 + 1 else f.2.2)
  behind f := (!f.1, f.2.1, if f.1 then f.2.2 else f.2.2 - 1)
  ahead_left c := by rcases c with ⟨b, i, j⟩; cases b <;> simp
  behind_right c := by rcases c with ⟨b, i, j⟩; cases b <;> simp
  Δ := Δy

/-- On the periodic staggered grid all faces are inner, so that the boundary hypotheses of
`theorem_1_mass` and `theorem_3` are empty there. -/
theorem periodic_inner (Nx Ny : ℕ) (Δx Δy : ℝ) (f : Node Nx Ny) :
    (periodicX Nx Ny Δx).IsInner f ∧ (periodicY Nx Ny Δy).IsInner f := by
  rcases f with ⟨b, i, j⟩
  cases b <;> simp [Stencil.IsInner, periodicX, periodicY]

section Formulas

variable {Nx Ny : ℕ} (Δx Δy : ℝ) (i : ZMod Nx) (j : ZMod Ny) (u g : Node Nx Ny → ℝ)

/-- The operators are the ones of the paper: `δ⁰_x` at `(x_{i+½}, y_j)`. -/
example :
    (periodicX Nx Ny Δx).δ u (false, i, j) = (u (false, i + 1, j) - u (false, i, j)) / Δx := by
  simp [Stencil.δ, periodicX]

/-- `δ⁰_x` at `(x_i, y_{j+½})`. -/
example : (periodicX Nx Ny Δx).δ u (true, i, j) = (u (true, i, j) - u (true, i - 1, j)) / Δx := by
  simp [Stencil.δ, periodicX]

/-- `δ⁰_y` at `(x_{i+½}, y_j)`. -/
example :
    (periodicY Nx Ny Δy).δ u (false, i, j) = (u (true, i, j) - u (true, i, j - 1)) / Δy := by
  simp [Stencil.δ, periodicY]

/-- `δ⁰_y` at `(x_i, y_{j+½})`. -/
example :
    (periodicY Nx Ny Δy).δ u (true, i, j) = (u (false, i, j + 1) - u (false, i, j)) / Δy := by
  simp [Stencil.δ, periodicY]

/-- `𝒟⁰_x` at the centre `(x_i, y_j)`. -/
example :
    (periodicX Nx Ny Δx).D0 g (false, i, j) = (g (false, i, j) - g (false, i - 1, j)) / Δx := by
  simp [Stencil.D0, periodicX]

/-- `𝒟⁰_x` at the corner `(x_{i+½}, y_{j+½})`. -/
example : (periodicX Nx Ny Δx).D0 g (true, i, j) = (g (true, i + 1, j) - g (true, i, j)) / Δx := by
  simp [Stencil.D0, periodicX]

/-- `𝒟⁰_y` at the centre `(x_i, y_j)`. -/
example : (periodicY Nx Ny Δy).D0 g (false, i, j) = (g (true, i, j) - g (true, i, j - 1)) / Δy := by
  simp [Stencil.D0, periodicY]

/-- `𝒟⁰_y` at the corner `(x_{i+½}, y_{j+½})`. -/
example :
    (periodicY Nx Ny Δy).D0 g (true, i, j) = (g (false, i, j + 1) - g (false, i, j)) / Δy := by
  simp [Stencil.D0, periodicY]

/-- `𝒟⁺_x` and `𝒟⁻_x` on the faces `(x_{i+½}, y_j)`. -/
example : (periodicX Nx Ny Δx).Dp g (false, i, j) = (g (false, i + 1, j) - g (false, i, j)) / Δx ∧
    (periodicX Nx Ny Δx).Dm g (false, i, j) = (g (false, i, j) - g (false, i - 1, j)) / Δx := by
  simp [Stencil.Dp, Stencil.Dm, Stencil.next, Stencil.prev, periodicX]

/-- `𝒟⁺_y` and `𝒟⁻_y` on the faces `(x_{i+½}, y_j)`. -/
example : (periodicY Nx Ny Δy).Dp g (false, i, j) = (g (false, i, j + 1) - g (false, i, j)) / Δy ∧
    (periodicY Nx Ny Δy).Dm g (false, i, j) = (g (false, i, j) - g (false, i, j - 1)) / Δy := by
  simp [Stencil.Dp, Stencil.Dm, Stencil.next, Stencil.prev, periodicY]

/-- `𝒟⁺_x` and `𝒟⁺_y` on the faces `(x_i, y_{j+½})`. -/
example : (periodicX Nx Ny Δx).Dp g (true, i, j) = (g (true, i + 1, j) - g (true, i, j)) / Δx ∧
    (periodicY Nx Ny Δy).Dp g (true, i, j) = (g (true, i, j + 1) - g (true, i, j)) / Δy := by
  simp [Stencil.Dp, Stencil.next, periodicX, periodicY]

end Formulas

/-! ### The asymptotic limit of the full-rank scheme -/

/-- The equation `k x + a x⁴ = ρ` has a nonnegative solution for `ρ ≥ 0`. -/
theorem exists_root {k a ρ : ℝ} (hk : 0 < k) (ha : 0 ≤ a) (hρ : 0 ≤ ρ) :
    ∃ x, 0 ≤ x ∧ k * x + a * x ^ 4 = ρ := by
  have hcont : ContinuousOn (fun t : ℝ => k * t + a * t ^ 4) (Set.Icc 0 (ρ / k)) := by fun_prop
  have hle : (0 : ℝ) ≤ ρ / k := by positivity
  have hmem : ρ ∈ Set.Icc ((fun t : ℝ => k * t + a * t ^ 4) 0)
      ((fun t : ℝ => k * t + a * t ^ 4) (ρ / k)) := by
    constructor
    · simpa using hρ
    · have e : k * (ρ / k) = ρ := by field_simp
      have : 0 ≤ a * (ρ / k) ^ 4 := by positivity
      simp only [e]
      linarith
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hle hcont hmem
  exact ⟨t, ht.1, hte⟩

/-- The scalar core of the limit `ε → 0`: on `x ≥ 0` the map `x ↦ k x + a x⁴` is expanding, so
that a family of nonnegative solutions of a perturbed equation converges to the unique nonnegative
solution of the limit equation, which exists. -/
theorem tendsto_of_expanding {l : Filter ℝ} [l.NeBot] {k a ρ₀ y₀ : ℝ} (hk : 0 < k) (ha : 0 ≤ a)
    {x τ y ρ : ℝ → ℝ} (hx : ∀ᶠ e in l, 0 ≤ x e) (hτ : Tendsto τ l (𝓝 0))
    (hτ0 : ∀ᶠ e in l, 0 ≤ τ e) (hy : Tendsto y l (𝓝 y₀)) (hρ : Tendsto ρ l (𝓝 ρ₀))
    (heq : ∀ᶠ e in l, k * x e + a * x e ^ 4 + k * τ e * (x e - y e) = ρ e) :
    ∃ x₀, 0 ≤ x₀ ∧ k * x₀ + a * x₀ ^ 4 = ρ₀ ∧ Tendsto x l (𝓝 x₀) := by
  -- boundedness
  have hb : Tendsto (fun e => (ρ e + k * τ e * y e) / k) l (𝓝 ((ρ₀ + k * 0 * y₀) / k)) :=
    ((hρ.add ((hτ.const_mul k).mul hy))).div_const k
  have hbound : ∀ᶠ e in l, x e ≤ (ρ₀ + k * 0 * y₀) / k + 1 := by
    filter_upwards [hb.eventually_lt_const (lt_add_one _), hx, hτ0, heq] with e h1 h2 h3 h4
    refine le_trans ?_ h1.le
    rw [le_div_iff₀ hk]
    have h5 : 0 ≤ a * x e ^ 4 := by positivity
    have h6 : 0 ≤ k * τ e * x e := by positivity
    nlinarith
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ e in l, |x e - y e| ≤ C := by
    have hy' : Tendsto (fun e => |y e|) l (𝓝 |y₀|) := hy.abs
    refine ⟨(ρ₀ + k * 0 * y₀) / k + 1 + (|y₀| + 1), ?_⟩
    filter_upwards [hy'.eventually_lt_const (lt_add_one _), hbound, hx] with e h1 h2 h3
    calc |x e - y e| ≤ |x e| + |y e| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h3]; linarith
  -- the perturbation vanishes
  have hw : Tendsto (fun e => k * τ e * (x e - y e)) l (𝓝 0) := by
    have h0 : Tendsto (fun e => k * τ e * C) l (𝓝 (k * 0 * C)) := (hτ.const_mul k).mul_const C
    rw [mul_zero, zero_mul] at h0
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hC, hτ0] with e h1 h2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hk.le h2)]
    exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hk.le h2)
  have hΨ : Tendsto (fun e => k * x e + a * x e ^ 4) l (𝓝 ρ₀) := by
    have := hρ.sub hw
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [heq] with e he
    linarith
  have hρ0 : 0 ≤ ρ₀ := by
    refine ge_of_tendsto hΨ ?_
    filter_upwards [hx] with e he
    positivity
  -- existence of the limit
  obtain ⟨x₀, hx₀, hxe⟩ := exists_root hk ha hρ0
  refine ⟨x₀, hx₀, hxe, ?_⟩
  -- convergence
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun e => |k * x e + a * x e ^ 4 - ρ₀| / k) l (𝓝 (|ρ₀ - ρ₀| / k)) :=
    ((hΨ.sub_const ρ₀).abs).div_const k
  rw [sub_self, abs_zero, zero_div] at h0
  refine squeeze_zero' (Eventually.of_forall fun e => norm_nonneg _) ?_ h0
  filter_upwards [hx] with e he
  rw [Real.norm_eq_abs, le_div_iff₀ hk, ← hxe]
  have hmono : ∀ {p q : ℝ}, 0 ≤ p → p ≤ q → 0 ≤ a * q ^ 4 - a * p ^ 4 := fun hp hpq => by
    have := pow_le_pow_left₀ hp hpq 4
    nlinarith
  rcases le_total (x e) x₀ with hle | hle
  · have := hmono he hle
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]
    nlinarith
  · have := hmono hx₀ hle
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
    nlinarith

namespace Setup

variable (P : Setup C F ι)

/-- The limit flux `-(Σᵗ)⁻¹ (Q_x 𝟙 δ⁰_x + Q_y 𝟙 δ⁰_y) B(T)`. -/
def limitFlux (T : C → ℝ) (f : F) (ℓ : ι) : ℝ :=
  -(1 / P.σt f) * (P.Ωx ℓ * P.x.δ (fun z => P.B (T z)) f + P.Ωy ℓ * P.y.δ (fun z => P.B (T z)) f)

/-- The discrete Rosseland equation (3.6) of arXiv 2502.20883, between the temperatures `T = Tⁿ` and
`T' = T^{n+1}`, at all centres and corners. -/
def IsRosseland (T T' : C → ℝ) : Prop :=
  ∀ z, P.cν / P.Δt * (T' z - T z) + 2 * π / (P.c * P.Δt) * (P.B (T' z) - P.B (T z)) =
    2 * π / 3 * (P.x.D0 (fun f => 1 / P.σt f * P.x.δ (fun z => P.B (T z)) f) z
      + P.y.D0 (fun f => 1 / P.σt f * P.y.δ (fun z => P.B (T z)) f) z)

variable {P} [Fintype ι]

/-- The moment computation of the proof of Theorem 2 of arXiv 2502.20883. -/
theorem wQD_limitFlux (hQ2 : P.IsSecondOrder) (T : C → ℝ) (z : C) :
    P.wQD P.x P.Ωx (P.limitFlux T) z + P.wQD P.y P.Ωy (P.limitFlux T) z =
      -(2 * π / 3 * (P.x.D0 (fun f => 1 / P.σt f * P.x.δ (fun z => P.B (T z)) f) z
        + P.y.D0 (fun f => 1 / P.σt f * P.y.δ (fun z => P.B (T z)) f) z)) := by
  set a : F → ℝ := fun f => 1 / P.σt f * P.x.δ (fun z => P.B (T z)) f with ha
  set b : F → ℝ := fun f => 1 / P.σt f * P.y.δ (fun z => P.B (T z)) f with hb
  have hD : ∀ (s : Stencil C F) ℓ, s.D0 (fun f => P.limitFlux T f ℓ) z =
      -(P.Ωx ℓ * s.D0 a z + P.Ωy ℓ * s.D0 b z) := fun s ℓ => by
    simp only [Stencil.D0, limitFlux, ha, hb]
    ring
  have ex : ∀ ℓ, P.w ℓ * P.Ωx ℓ * P.x.D0 (fun f => P.limitFlux T f ℓ) z =
      -(P.w ℓ * (P.Ωx ℓ * P.Ωx ℓ) * P.x.D0 a z + P.w ℓ * (P.Ωx ℓ * P.Ωy ℓ) * P.x.D0 b z) :=
    fun ℓ => by rw [hD]; ring
  have ey : ∀ ℓ, P.w ℓ * P.Ωy ℓ * P.y.D0 (fun f => P.limitFlux T f ℓ) z =
      -(P.w ℓ * (P.Ωx ℓ * P.Ωy ℓ) * P.y.D0 a z + P.w ℓ * (P.Ωy ℓ * P.Ωy ℓ) * P.y.D0 b z) :=
    fun ℓ => by rw [hD]; ring
  simp only [wQD, ex, ey, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hQ2.sum_ΩxΩx, hQ2.sum_ΩyΩy, hQ2.sum_ΩxΩy]
  ring

end Setup

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- `wᵀ Q 𝒟⁰ g` is continuous in `g`. -/
theorem continuous_wQD (s : Stencil C F) (Ω : ι → ℝ) (z : C) :
    Continuous fun G : F → ι → ℝ => P.wQD s Ω G z := by
  unfold wQD Stencil.D0
  fun_prop

/-- `(I - (1/2π) 𝟙 wᵀ) ℒ g` is continuous in `g`. -/
theorem continuous_meanFree_transport (f : F) (ℓ : ι) :
    Continuous fun G : F → ι → ℝ => P.meanFree (P.transport G f) ℓ := by
  unfold meanFree transport Stencil.upwind Stencil.Dp Stencil.Dm
  fun_prop

/-- The limit of the macro equations: if the fluxes `g'` converge to `G` as `ε → 0` and the data
converge, then every family of nonnegative temperatures `T'` converges, and so does `h'`.  This is
the second half of the proofs of Theorems 2 and 5 of arXiv 2502.20883.  The limit is the unique
nonnegative solution of the macro equations with `ε = 0`; the convergence of `T'`, which the paper
takes for granted, is derived from the monotonicity of `T ↦ c_ν T + a T⁴`. -/
theorem macro_limit [Fintype C] {σ₀ : ℝ} (hA : P.IsAdmissible σ₀) (hσa : ∀ z, 0 < P.σa z)
    {g' : ℝ → F → ι → ℝ} {h h' T T' : ℝ → C → ℝ} {G : F → ι → ℝ} {h₀ T₀ : C → ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsMacroStep ε (h ε) (T ε) (g' ε) (h' ε) (T' ε))
    (hg' : Tendsto g' (𝓝[>] 0) (𝓝 G)) (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀))
    (hT : Tendsto T (𝓝[>] 0) (𝓝 T₀)) (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z, 0 ≤ T' ε z) :
    ∃ T₁ h₁ : C → ℝ, Tendsto T' (𝓝[>] 0) (𝓝 T₁) ∧ Tendsto h' (𝓝[>] 0) (𝓝 h₁) ∧ (∀ z, 0 ≤ T₁ z) ∧
      ∀ z, P.cν / P.Δt * (T₁ z - T₀ z) + 2 * π / (P.c * P.Δt) * (P.B (T₁ z) - P.B (T₀ z)) =
        -(P.wQD P.x P.Ωx G z + P.wQD P.y P.Ωy G z) := by
  have hπ := Real.pi_pos
  have hc := hA.c_pos
  have hcν := hA.cν_pos
  have hΔt := hA.Δt_pos
  have ha := hA.a_nonneg
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hk : 0 < P.cν / P.Δt := by positivity
  have ha' : 0 ≤ P.a / P.Δt := by positivity
  have hTz : ∀ z, Tendsto (fun ε => T ε z) (𝓝[>] 0) (𝓝 (T₀ z)) := tendsto_pi_nhds.1 hT
  have hhz : ∀ z, Tendsto (fun ε => h ε z) (𝓝[>] 0) (𝓝 (h₀ z)) := tendsto_pi_nhds.1 hh
  have hR : ∀ z, Tendsto (fun ε => P.wQD P.x P.Ωx (g' ε) z + P.wQD P.y P.Ωy (g' ε) z)
      (𝓝[>] 0) (𝓝 (P.wQD P.x P.Ωx G z + P.wQD P.y P.Ωy G z)) := fun z =>
    (((continuous_wQD _ _ z).tendsto G).comp hg').add
      (((continuous_wQD _ _ z).tendsto G).comp hg')
  have cell : ∀ z, ∃ x₀, 0 ≤ x₀ ∧ P.cν / P.Δt * x₀ + P.a / P.Δt * x₀ ^ 4 =
      P.cν / P.Δt * T₀ z + P.a / P.Δt * T₀ z ^ 4
        - (P.wQD P.x P.Ωx G z + P.wQD P.y P.Ωy G z) ∧
      Tendsto (fun ε => T' ε z) (𝓝[>] 0) (𝓝 x₀) := by
    intro z
    have hσ := hσa z
    have hρ : Tendsto (fun ε => P.cν / P.Δt * T ε z + P.a / P.Δt * T ε z ^ 4
        - (P.wQD P.x P.Ωx (g' ε) z + P.wQD P.y P.Ωy (g' ε) z)
        + 2 * π * ε ^ 2 / (P.c * P.Δt) * h ε z) (𝓝[>] 0)
        (𝓝 (P.cν / P.Δt * T₀ z + P.a / P.Δt * T₀ z ^ 4
          - (P.wQD P.x P.Ωx G z + P.wQD P.y P.Ωy G z)
          + 2 * π * 0 ^ 2 / (P.c * P.Δt) * h₀ z)) :=
      ((((hTz z).const_mul _).add (((hTz z).pow 4).const_mul _)).sub (hR z)).add
        ((((hε.pow 2).const_mul (2 * π)).div_const _).mul (hhz z))
    have e0 : 2 * π * (0 : ℝ) ^ 2 / (P.c * P.Δt) * h₀ z = 0 := by simp
    rw [e0, add_zero] at hρ
    have hτ : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.σa z * P.Δt)) (𝓝[>] 0) (𝓝 0) := by
      have := (hε.pow 2).div_const (P.c * P.σa z * P.Δt)
      simpa using this
    refine tendsto_of_expanding hk ha' ?_ hτ ?_ (hTz z) hρ ?_
    · filter_upwards [hpos] with ε he using he z
    · exact Eventually.of_forall fun ε => by positivity
    · filter_upwards [hstep] with ε hs
      have e1 := hs.h_eq z
      have e2 := hs.T_eq z
      simp only [B] at e1
      linear_combination (norm := (field_simp; ring))
        (2 * π) * e1 + (1 + ε ^ 2 / (P.c * P.σa z * P.Δt)) * e2
  choose x₀ hx0 hx1 hx2 using cell
  refine ⟨x₀, fun z => P.cν / P.Δt * (x₀ z - T₀ z) / (2 * π * P.σa z), tendsto_pi_nhds.2 hx2, ?_,
    hx0, ?_⟩
  · rw [tendsto_pi_nhds]
    intro z
    have hσ := hσa z
    have : Tendsto (fun ε => P.cν / P.Δt * (T' ε z - T ε z) / (2 * π * P.σa z)) (𝓝[>] 0)
        (𝓝 (P.cν / P.Δt * (x₀ z - T₀ z) / (2 * π * P.σa z))) :=
      (((hx2 z).sub (hTz z)).const_mul _).div_const _
    refine this.congr' ?_
    filter_upwards [hstep] with ε hs
    rw [hs.T_eq z]
    field_simp
  · intro z
    have e := hx1 z
    simp only [B]
    field_simp at e ⊢
    linear_combination e

/-- `δ⁰ (B + ε² h) → δ⁰ B` as `ε → 0`. -/
theorem tendsto_δ_phi {h : ℝ → C → ℝ} {T : ℝ → C → ℝ} {h₀ T₀ : C → ℝ}
    (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀)) (hT : Tendsto T (𝓝[>] 0) (𝓝 T₀)) (s : Stencil C F) (f : F) :
    Tendsto (fun ε => s.δ (P.phi ε (h ε) (T ε)) f) (𝓝[>] 0) (𝓝 (s.δ (fun z => P.B (T₀ z)) f)) := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hφ : ∀ z, Tendsto (fun ε => P.phi ε (h ε) (T ε) z) (𝓝[>] 0) (𝓝 (P.B (T₀ z))) := fun z => by
    have hB : Continuous P.B := by
      unfold B
      fun_prop
    have h1 := (hB.tendsto (T₀ z)).comp (tendsto_pi_nhds.1 hT z)
    have h2 := (hε.pow 2).mul (tendsto_pi_nhds.1 hh z)
    have h3 := h1.add h2
    simpa [phi] using h3
  exact ((hφ _).sub (hφ _)).div_const _

/-- The limit of the micro equation (3.3a) as `ε → 0` at fixed `Δt`, for data that converge. -/
theorem micro_limit {σ₀ : ℝ} (hA : P.IsAdmissible σ₀) (hσ₀ : 0 < σ₀) (hper : ∀ f, P.Inner f)
    {g g' : ℝ → F → ι → ℝ} {h h' T T' : ℝ → C → ℝ} {g₀ : F → ι → ℝ} {h₀ T₀ : C → ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsStep ε (g ε) (h ε) (T ε) (g' ε) (h' ε) (T' ε))
    (hg : Tendsto g (𝓝[>] 0) (𝓝 g₀)) (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀))
    (hT : Tendsto T (𝓝[>] 0) (𝓝 T₀)) : Tendsto g' (𝓝[>] 0) (𝓝 (P.limitFlux T₀)) := by
  have hc := hA.c_pos
  have hΔt := hA.Δt_pos
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hκ : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hε.pow 2).div_const (P.c * P.Δt)
  have hδ := fun s f => tendsto_δ_phi (P := P) hh hT s f
  rw [tendsto_pi_nhds]
  intro f
  rw [tendsto_pi_nhds]
  intro ℓ
  have hσ : 0 < P.σt f := hσ₀.trans_le (hA.σ₀_le f)
  have hgz : Tendsto (fun ε => g ε f ℓ) (𝓝[>] 0) (𝓝 (g₀ f ℓ)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hg f) ℓ
  have hMF := ((continuous_meanFree_transport (P := P) f ℓ).tendsto g₀).comp hg
  have hlim := (((((hκ.mul hgz).sub (hε.mul hMF)).sub ((hδ P.x f).const_mul (P.Ωx ℓ))).sub
    ((hδ P.y f).const_mul (P.Ωy ℓ)))).div (hκ.add_const (P.σt f)) (by simpa using hσ.ne')
  have e : (0 * g₀ f ℓ - 0 * P.meanFree (P.transport g₀ f) ℓ
      - P.Ωx ℓ * P.x.δ (fun z => P.B (T₀ z)) f - P.Ωy ℓ * P.y.δ (fun z => P.B (T₀ z)) f)
        / (0 + P.σt f) = P.limitFlux T₀ f ℓ := by
    simp only [limitFlux]
    field_simp
    ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [hstep, self_mem_nhdsWithin] with ε hs hε0
  have hE := hs.g_eq f (hper f) ℓ
  rw [MicroEq] at hE
  have hε1 : (0 : ℝ) < ε := hε0
  have hne : ε ^ 2 / (P.c * P.Δt) + P.σt f ≠ 0 := by positivity
  simp only [Pi.div_apply]
  rw [div_eq_iff hne]
  simp only [Function.comp]
  linear_combination -hE

/-- **Theorem 2 of arXiv 2502.20883** (asymptotic preservation, full-rank scheme), for one step with
convergent data: as `ε → 0` at fixed `Δt`, `g^{n+1} → -(1/σ^t)(Q_x 𝟙 δ⁰_x + Q_y 𝟙 δ⁰_y) Bⁿ`, and
`T^{n+1}`, `h^{n+1}` converge to a solution of the discrete Rosseland equation (3.6).  Differences
from the paper, whose proof is formal: `ε → 0` is an actual limit; the only assumption on the family
is `T^{n+1} ≥ 0` for small `ε`, and the convergence of `T^{n+1}` and `h^{n+1}` is derived.  The
hypotheses `σ^t ≥ σ₀ > 0` and `σ^a > 0` are the paper's.  The grid is periodic (all faces inner);
zero boundary conditions change the limit at the cells next to the boundary. -/
theorem theorem_2_step [Fintype C] {σ₀ : ℝ} (hQ2 : P.IsSecondOrder) (hA : P.IsAdmissible σ₀)
    (hσ₀ : 0 < σ₀) (hσa : ∀ z, 0 < P.σa z) (hper : ∀ f, P.Inner f)
    {g g' : ℝ → F → ι → ℝ} {h h' T T' : ℝ → C → ℝ} {g₀ : F → ι → ℝ} {h₀ T₀ : C → ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P.IsStep ε (g ε) (h ε) (T ε) (g' ε) (h' ε) (T' ε))
    (hg : Tendsto g (𝓝[>] 0) (𝓝 g₀)) (hh : Tendsto h (𝓝[>] 0) (𝓝 h₀))
    (hT : Tendsto T (𝓝[>] 0) (𝓝 T₀)) (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z, 0 ≤ T' ε z) :
    Tendsto g' (𝓝[>] 0) (𝓝 (P.limitFlux T₀)) ∧
      ∃ T₁ h₁ : C → ℝ, Tendsto T' (𝓝[>] 0) (𝓝 T₁) ∧ Tendsto h' (𝓝[>] 0) (𝓝 h₁) ∧
        (∀ z, 0 ≤ T₁ z) ∧ P.IsRosseland T₀ T₁ := by
  have hlim := micro_limit hA hσ₀ hper hstep hg hh hT
  refine ⟨hlim, ?_⟩
  obtain ⟨T₁, h₁, h1, h2, h3, h4⟩ := macro_limit hA hσa (hstep.mono fun ε hs => hs.toIsMacroStep)
    hlim hh hT hpos
  refine ⟨T₁, h₁, h1, h2, h3, fun z => ?_⟩
  rw [h4 z, wQD_limitFlux hQ2, neg_neg]

/-- **Theorem 2 of arXiv 2502.20883** along a whole trajectory: starting from data that converge
(for instance data independent of `ε`), the temperatures of the scheme converge at every time level
to a solution of the explicit discrete Rosseland scheme (3.6). -/
theorem theorem_2 [Fintype C] {σ₀ : ℝ} (hQ2 : P.IsSecondOrder) (hA : P.IsAdmissible σ₀)
    (hσ₀ : 0 < σ₀) (hσa : ∀ z, 0 < P.σa z) (hper : ∀ f, P.Inner f)
    {g : ℕ → ℝ → F → ι → ℝ} {h T : ℕ → ℝ → C → ℝ} {g₀ : F → ι → ℝ} {h₀ T₀ : C → ℝ}
    (hstep : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P.IsStep ε (g n ε) (h n ε) (T n ε) (g (n + 1) ε) (h (n + 1) ε) (T (n + 1) ε))
    (hg : Tendsto (g 0) (𝓝[>] 0) (𝓝 g₀)) (hh : Tendsto (h 0) (𝓝[>] 0) (𝓝 h₀))
    (hT : Tendsto (T 0) (𝓝[>] 0) (𝓝 T₀))
    (hpos : ∀ n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z, 0 ≤ T (n + 1) ε z) :
    ∃ U : ℕ → C → ℝ, U 0 = T₀ ∧ (∀ n, Tendsto (T n) (𝓝[>] 0) (𝓝 (U n))) ∧
      (∀ n, Tendsto (g (n + 1)) (𝓝[>] 0) (𝓝 (P.limitFlux (U n)))) ∧
      (∀ n z, 0 ≤ U (n + 1) z) ∧ ∀ n, P.IsRosseland (U n) (U (n + 1)) := by
  have key : ∀ n, ∃ (G : F → ι → ℝ) (H X : C → ℝ), Tendsto (g n) (𝓝[>] 0) (𝓝 G) ∧
      Tendsto (h n) (𝓝[>] 0) (𝓝 H) ∧ Tendsto (T n) (𝓝[>] 0) (𝓝 X) ∧ (n = 0 → X = T₀) := by
    intro n
    induction n with
    | zero => exact ⟨g₀, h₀, T₀, hg, hh, hT, fun _ => rfl⟩
    | succ n ih =>
      obtain ⟨G, H, X, h1, h2, h3, -⟩ := ih
      obtain ⟨h4, T₁, h₁, h5, h6, -, -⟩ :=
        theorem_2_step hQ2 hA hσ₀ hσa hper (hstep n) h1 h2 h3 (hpos n)
      exact ⟨_, h₁, T₁, h4, h6, h5, fun h => absurd h (Nat.succ_ne_zero n)⟩
  choose G H X h1 h2 h3 h4 using key
  have hall := fun n => theorem_2_step hQ2 hA hσ₀ hσa hper (hstep n) (h1 n) (h2 n) (h3 n) (hpos n)
  refine ⟨X, h4 0 rfl, h3, fun n => (hall n).1, ?_, ?_⟩
  · intro n z
    obtain ⟨-, T₁, h₁, h5, -, h6, -⟩ := hall n
    rw [tendsto_nhds_unique (h3 (n + 1)) h5]
    exact h6 z
  · intro n
    obtain ⟨-, T₁, h₁, h5, -, -, h6⟩ := hall n
    rw [tendsto_nhds_unique (h3 (n + 1)) h5]
    exact h6

end Setup

/-! ### The low-rank scheme: Theorems 4 and 5 -/

section LowRank

open Matrix

/-- The matrix `𝐃⁰_v` of `𝒟⁰_v`. -/
def Stencil.D0mat [DecidableEq F] (s : Stencil C F) : Matrix C F ℝ :=
  Matrix.of fun z f => ((if f = s.right z then 1 else 0) - (if f = s.left z then 1 else 0)) / s.Δ

/-- The matrix `𝐃⁰_v` acts as `𝒟⁰_v`. -/
theorem Stencil.D0mat_mulVec [Fintype F] [DecidableEq F] (s : Stencil C F) (a : F → ℝ) (z : C) :
    (s.D0mat *ᵥ a) z = s.D0 a z := by
  simp only [mulVec, dotProduct, Stencil.D0mat, Matrix.of_apply, Stencil.D0, div_mul_eq_mul_div,
    sub_mul, ite_mul, one_mul, zero_mul, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

namespace Setup

variable {P : Setup C F ι} [Fintype ι] {r : Type*} [Fintype r]

/-- `𝐃⁰_v G Q_v w = wᵀ Q_v 𝒟⁰_v G`, the matrix form of the flux divergence. -/
theorem D0mat_mulVec_mul_diagonal [Fintype F] [DecidableEq F] [DecidableEq ι] (s : Stencil C F)
    (Ω : ι → ℝ) (G : Matrix F ι ℝ) (z : C) :
    (s.D0mat *ᵥ ((G * diagonal Ω) *ᵥ P.w)) z = P.wQD s Ω (fun f ℓ => G f ℓ) z := by
  rw [Stencil.D0mat_mulVec, wQD_eq_D0]
  congr 1
  ext f
  simp only [mulVec, dotProduct, mul_diagonal]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- **Theorem 4 of arXiv 2502.20883** (local mass conservation of the macro–micro parallel BUG
scheme): the discrete conservation law in the matrix form of the paper,
`(Φ^{n+1} - Φⁿ) / (c Δt) + (1/2π) ∑_v 𝐃⁰_v X S Vᵀ Q_v w = -Σ^a h^{n+1}`.  The law only involves the
macro equations, so that nothing about the factors `X`, `S`, `V` is needed. -/
theorem theorem_4 [Fintype F] [DecidableEq F] [DecidableEq ι] {ε : ℝ} {h T h' T' : C → ℝ}
    (X : Matrix F r ℝ) (S : Matrix r r ℝ) (V : Matrix ι r ℝ)
    (hs : P.IsMacroStep ε h T (fun f ℓ => (X * S * Vᵀ) f ℓ) h' T') (z : C) :
    1 / (P.c * P.Δt) * (P.phi ε h' T' z - P.phi ε h T z)
        + 1 / (2 * π) * (P.x.D0mat *ᵥ ((X * S * Vᵀ * diagonal P.Ωx) *ᵥ P.w)) z
        + 1 / (2 * π) * (P.y.D0mat *ᵥ ((X * S * Vᵀ * diagonal P.Ωy) *ᵥ P.w)) z = -P.σa z * h' z ∧
      P.cν / P.Δt * (T' z - T z) = 2 * π * P.σa z * h' z := by
  rw [D0mat_mulVec_mul_diagonal, D0mat_mulVec_mul_diagonal]
  exact theorem_1 hs z

/-- **Theorem 4 of arXiv 2502.20883**, the conservation of the total mass, for zero and for periodic
boundary conditions. -/
theorem theorem_4_mass [Fintype C] [Fintype F] {ε : ℝ} {h T h' T' : C → ℝ}
    (hc : P.c ≠ 0) (hΔt : P.Δt ≠ 0) (X : Matrix F r ℝ) (S : Matrix r r ℝ) (V : Matrix ι r ℝ)
    (hs : P.IsMacroStep ε h T (fun f ℓ => (X * S * Vᵀ) f ℓ) h' T')
    (hg' : ∀ f, ¬ P.Inner f → ∀ ℓ, (X * S * Vᵀ) f ℓ = 0) : P.mass ε h' T' = P.mass ε h T :=
  theorem_1_mass hc hΔt hs hg'

end Setup

/-- The square of the Frobenius norm. -/
def frob2 {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

open scoped LeanDLRA.Frobenius in
/-- **Bridge.** `frob2 A` is the squared core Frobenius norm `‖A‖²` (`Frobenius.norm_sq_eq_sum`). -/
theorem frob2_eq_norm_sq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    frob2 A = ‖A‖ ^ 2 :=
  (Frobenius.norm_sq_eq_sum A).symm

/-- Limits of matrix products. -/
theorem tendsto_matrix_mul {a b c : Type*} [Fintype b] {l : Filter ℝ} {A : ℝ → Matrix a b ℝ}
    {B : ℝ → Matrix b c ℝ} {A₀ : Matrix a b ℝ} {B₀ : Matrix b c ℝ} (hA : Tendsto A l (𝓝 A₀))
    (hB : Tendsto B l (𝓝 B₀)) : Tendsto (fun e => A e * B e) l (𝓝 (A₀ * B₀)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (A₀, B₀)).comp (hA.prodMk_nhds hB)

/-- The solutions of the shifted systems `(κ + M) Z = R` converge, as `κ → 0`, to the solution of
`M Z = R₀`, for an invertible `M`.  This is the `ε → 0` limit of the K-, L- and S-steps. -/
theorem tendsto_shifted {n m : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hM : M.det ≠ 0) {l : Filter ℝ} {κ : ℝ → ℝ} (hκ : Tendsto κ l (𝓝 0)) {Z R : ℝ → Matrix n m ℝ}
    {W R₀ : Matrix n m ℝ} (hR : Tendsto R l (𝓝 R₀)) (hW : M * W = R₀)
    (heq : ∀ᶠ e in l, (κ e • (1 : Matrix n n ℝ) + M) * Z e = R e) : Tendsto Z l (𝓝 W) := by
  set B : ℝ → Matrix n n ℝ := fun e => κ e • 1 + M with hBdef
  have hB : Tendsto B l (𝓝 M) := by
    have := (hκ.smul_const (1 : Matrix n n ℝ)).add_const M
    simpa using this
  have hdet : Tendsto (fun e => (B e).det) l (𝓝 M.det) :=
    ((continuous_id.matrix_det).tendsto M).comp hB
  have hadj : Tendsto (fun e => (B e).adjugate) l (𝓝 M.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto M).comp hB
  have hprod : Tendsto (fun e => (B e).det⁻¹ • ((B e).adjugate * R e)) l
      (𝓝 (M.det⁻¹ • (M.adjugate * R₀))) :=
    (hdet.inv₀ hM).smul (tendsto_matrix_mul hadj hR)
  have e0 : ∀ (D : Matrix n n ℝ) (U : Matrix n m ℝ), D.det ≠ 0 →
      D.det⁻¹ • (D.adjugate * (D * U)) = U := fun D U hD => by
    rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hD, one_smul]
  rw [← hW, e0 M W hM] at hprod
  refine hprod.congr' ?_
  filter_upwards [heq, hdet.eventually_ne hM] with e h1 h2
  rw [← h1]
  exact e0 _ _ h2

/-- `Û Ŝ V̂ᵀ` with `Û = [X, X̃]`, `V̂ = [V, Ṽ]` and `Ŝ = [[S̄, S̃ᴸ], [S̃ᴷ, 0]]`, `S̃ᴷ = X̃ᵀ K'`,
`S̃ᴸ = L'ᵀ Ṽ`: the augmented solution of step 3 of the scheme of Section 4 of arXiv 2502.20883. -/
def augmented {r : Type*} [Fintype r] [Fintype F] (X Xt : Matrix F r ℝ) [Fintype ι]
    (V Vt : Matrix ι r ℝ) (K' : Matrix F r ℝ) (L' : Matrix ι r ℝ) (Sb : Matrix r r ℝ) :
    Matrix F ι ℝ :=
  fromCols X Xt * fromBlocks Sb (L'ᵀ * Vt) (Xtᵀ * K') 0 * (fromCols V Vt)ᵀ

namespace Setup

variable (P : Setup C F ι) [Fintype ι]

/-- The explicit part `-ε ℒ(Y) (I - (1/2π) 𝟙 wᵀ)ᵀ - 𝐝⁰(B + ε² h) 𝟙ᵀ Q` of the right-hand side of the
time-continuous equation (4.1). -/
def rhs (ε : ℝ) (Y : Matrix F ι ℝ) (h T : C → ℝ) : Matrix F ι ℝ :=
  Matrix.of fun f ℓ => -ε * P.meanFree (P.transport Y f) ℓ
    - (P.Ωx ℓ * P.x.δ (P.phi ε h T) f + P.Ωy ℓ * P.y.δ (P.phi ε h T) f)

/-- The matrix of `limitFlux`, `-(Σᵗ)⁻¹ (𝐝⁰_x B 𝟙ᵀ Q_x + 𝐝⁰_y B 𝟙ᵀ Q_y)`. -/
def fluxMatrix (T : C → ℝ) : Matrix F ι ℝ := Matrix.of (P.limitFlux T)

variable {r p q : Type*} [Fintype r] [DecidableEq r] [Fintype p] [DecidableEq p] [Fintype q]
  [DecidableEq q] [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- The orthonormal matrices `A`, `W` contain the vectors `(Σᵗ)⁻¹ 𝐝⁰_v B(T)` and `Q_v 𝟙` in their
ranges.  For `A = X`, `W = V` this is what the pre-augmentation (step 1 of the scheme of Section 4
of arXiv 2502.20883) achieves. -/
structure Preserves (T : C → ℝ) (A : Matrix F p ℝ) (W : Matrix ι q ℝ) : Prop where
  A_orth : Aᵀ * A = 1
  W_orth : Wᵀ * W = 1
  grad_x : ∃ u, (fun f => 1 / P.σt f * P.x.δ (fun z => P.B (T z)) f) = A *ᵥ u
  grad_y : ∃ u, (fun f => 1 / P.σt f * P.y.δ (fun z => P.B (T z)) f) = A *ᵥ u
  Ωx_mem : ∃ u, P.Ωx = W *ᵥ u
  Ωy_mem : ∃ u, P.Ωy = W *ᵥ u

/-- The parallel update (4.2), (4.3), (4.4) from the (pre-augmented) factors `X`, `S`, `V`, and the
basis augmentation: `X̃`, `Ṽ` are such that `[X, X̃]`, `[V, Ṽ]` capture `K'`, `L'`.  Orthonormality
of the augmented bases is not needed, as in `matrix_parallelBUG_eq`. -/
structure IsParallelStep (ε : ℝ) (h T : C → ℝ) (X : Matrix F r ℝ) (S : Matrix r r ℝ)
    (V : Matrix ι r ℝ) (K' : Matrix F r ℝ) (L' : Matrix ι r ℝ) (Sb : Matrix r r ℝ)
    (Xt : Matrix F r ℝ) (Vt : Matrix ι r ℝ) : Prop where
  K_eq : (ε ^ 2 / (P.c * P.Δt)) • (K' - X * S) =
    P.rhs ε (X * S * Vᵀ) h T * V - diagonal P.σt * K'
  L_eq : (ε ^ 2 / (P.c * P.Δt)) • (L' - V * Sᵀ) =
    (P.rhs ε (X * S * Vᵀ) h T)ᵀ * X - L' * (Xᵀ * diagonal P.σt * X)
  S_eq : (ε ^ 2 / (P.c * P.Δt)) • (Sb - S) =
    Xᵀ * P.rhs ε (X * S * Vᵀ) h T * V - Xᵀ * diagonal P.σt * X * Sb
  X_cap : fromCols X Xt * (fromCols X Xt)ᵀ * K' = K'
  V_cap : fromCols V Vt * (fromCols V Vt)ᵀ * L' = L'

variable {P}

/-- `fluxMatrix` as a sum of two rank-one matrices. -/
theorem fluxMatrix_eq (T : C → ℝ) : P.fluxMatrix T =
    -(vecMulVec (fun f => 1 / P.σt f * P.x.δ (fun z => P.B (T z)) f) P.Ωx
      + vecMulVec (fun f => 1 / P.σt f * P.y.δ (fun z => P.B (T z)) f) P.Ωy) := by
  ext f ℓ
  simp only [fluxMatrix, limitFlux, Matrix.of_apply, Matrix.neg_apply, Matrix.add_apply,
    vecMulVec_apply]
  ring

/-- `A Aᵀ` fixes the range of an orthonormal `A`. -/
theorem mulVec_mul_transpose {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix F m ℝ}
    (hA : Aᵀ * A = 1) (u : m → ℝ) : (A * Aᵀ) *ᵥ (A *ᵥ u) = A *ᵥ u := by
  rw [mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]

/-- `G = (Σᵗ)⁻¹ 𝐝⁰ B 𝟙ᵀ Q` lies in the range of `A`. -/
theorem Preserves.left_fix {T : C → ℝ} {A : Matrix F p ℝ} {W : Matrix ι q ℝ}
    (h : P.Preserves T A W) : A * Aᵀ * P.fluxMatrix T = P.fluxMatrix T := by
  obtain ⟨u, hu⟩ := h.grad_x
  obtain ⟨v, hv⟩ := h.grad_y
  rw [fluxMatrix_eq, Matrix.mul_neg, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, hu, hv,
    mulVec_mul_transpose h.A_orth, mulVec_mul_transpose h.A_orth]

/-- `G = (Σᵗ)⁻¹ 𝐝⁰ B 𝟙ᵀ Q` has its rows in the range of `W`. -/
theorem Preserves.right_fix {T : C → ℝ} {A : Matrix F p ℝ} {W : Matrix ι q ℝ}
    (h : P.Preserves T A W) : P.fluxMatrix T * (W * Wᵀ) = P.fluxMatrix T := by
  obtain ⟨u, hu⟩ := h.Ωx_mem
  obtain ⟨v, hv⟩ := h.Ωy_mem
  have key : ∀ y : ι → ℝ, y = W *ᵥ (Wᵀ *ᵥ y) → y ᵥ* (W * Wᵀ) = y := fun y hy => by
    rw [← vecMul_vecMul, vecMul_transpose, ← mulVec_transpose, ← hy]
  have fix : ∀ u, W *ᵥ u = W *ᵥ (Wᵀ *ᵥ (W *ᵥ u)) := fun u => by
    rw [mulVec_mulVec u Wᵀ W, h.W_orth, one_mulVec]
  rw [fluxMatrix_eq, Matrix.neg_mul, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul,
    key _ (by rw [hu]; exact fix u), key _ (by rw [hv]; exact fix v)]

/-- `(Σᵗ) G` is the limit of `rhs` as `ε → 0`, with `G = fluxMatrix T`. -/
theorem diagonal_mul_fluxMatrix (hσ : ∀ f, P.σt f ≠ 0) (T : C → ℝ) :
    diagonal P.σt * P.fluxMatrix T = Matrix.of fun f ℓ =>
      -(P.Ωx ℓ * P.x.δ (fun z => P.B (T z)) f + P.Ωy ℓ * P.y.δ (fun z => P.B (T z)) f) := by
  ext f ℓ
  have := hσ f
  simp only [diagonal_mul, fluxMatrix, limitFlux, Matrix.of_apply]
  field_simp

/-- The limit of `rhs` as `ε → 0`, for fixed data. -/
theorem tendsto_rhs (Y : Matrix F ι ℝ) (h T : C → ℝ) :
    Tendsto (fun ε => P.rhs ε Y h T) (𝓝[>] 0) (𝓝 (Matrix.of fun f ℓ =>
      -(P.Ωx ℓ * P.x.δ (fun z => P.B (T z)) f + P.Ωy ℓ * P.y.δ (fun z => P.B (T z)) f))) := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine tendsto_pi_nhds.2 fun f => tendsto_pi_nhds.2 fun ℓ => ?_
  have h1 := tendsto_δ_phi (P := P) (tendsto_const_nhds (x := h)) (tendsto_const_nhds (x := T))
  have h2 := ((hε.neg.mul_const (P.meanFree (P.transport Y f) ℓ))).sub
    (((h1 P.x f).const_mul (P.Ωx ℓ)).add ((h1 P.y f).const_mul (P.Ωy ℓ)))
  simpa [rhs] using h2

/-- The limit of the parallel update: `Û Ŝ V̂ᵀ → G` as `ε → 0`, for `G = fluxMatrix T` and `X`
containing `(Σᵗ)⁻¹ 𝐝⁰ B`.  The rank condition on `Xᵀ Σᵗ X` that the proof of the paper assumes is
derived.  The augmented bases may depend on `ε` in any way, and the limit is taken for the matrix
`Û Ŝ V̂ᵀ`, which by `matrix_parallelBUG_eq` depends on them only through `K'`, `L'`, `S̄`. -/
theorem tendsto_augmented {σ₀ : ℝ} (hA : P.IsAdmissible σ₀) (hσ₀ : 0 < σ₀) {h T : C → ℝ}
    {X : Matrix F r ℝ} {S : Matrix r r ℝ} {V : Matrix ι r ℝ} (hXV : P.Preserves T X V)
    {K' Xt : ℝ → Matrix F r ℝ} {L' Vt : ℝ → Matrix ι r ℝ} {Sb : ℝ → Matrix r r ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P.IsParallelStep ε h T X S V (K' ε) (L' ε) (Sb ε) (Xt ε) (Vt ε)) :
    Tendsto (fun ε => augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε)) (𝓝[>] 0)
      (𝓝 (P.fluxMatrix T)) := by
  have hc := hA.c_pos
  have hΔt := hA.Δt_pos
  have hσ : ∀ f, 0 < P.σt f := fun f => hσ₀.trans_le (hA.σ₀_le f)
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hκ : Tendsto (fun ε : ℝ => ε ^ 2 / (P.c * P.Δt)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hε.pow 2).div_const (P.c * P.Δt)
  set G := P.fluxMatrix T with hG
  set E₀ : Matrix F ι ℝ := Matrix.of fun f ℓ =>
    -(P.Ωx ℓ * P.x.δ (fun z => P.B (T z)) f + P.Ωy ℓ * P.y.δ (fun z => P.B (T z)) f) with hE₀
  set E : ℝ → Matrix F ι ℝ := fun ε => P.rhs ε (X * S * Vᵀ) h T with hEdef
  have hE : Tendsto E (𝓝[>] 0) (𝓝 E₀) := tendsto_rhs _ h T
  have hSG : diagonal P.σt * G = E₀ := diagonal_mul_fluxMatrix (fun f => (hσ f).ne') T
  have hPX : X * Xᵀ * G = G := hXV.left_fix
  set M : Matrix r r ℝ := Xᵀ * diagonal P.σt * X with hM
  have hdetS : (diagonal P.σt : Matrix F F ℝ).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun f _ => (hσ f).ne'
  have hdetM : M.det ≠ 0 := by
    have hinj : Function.Injective X.mulVec := fun u v huv => by
      have := congrArg (fun y => Xᵀ *ᵥ y) huv
      simpa [mulVec_mulVec, hXV.A_orth] using this
    have hpd := (Matrix.posDef_diagonal_iff.2 hσ).conjTranspose_mul_mul_same hinj
    rw [conjTranspose_eq_transpose_of_trivial] at hpd
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hpd.isUnit).ne_zero
  have hMt : Mᵀ = M := by
    simp only [hM, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hK : Tendsto K' (𝓝[>] 0) (𝓝 (G * V)) := by
    refine tendsto_shifted (diagonal P.σt) hdetS hκ
      (R := fun ε => (ε ^ 2 / (P.c * P.Δt)) • (X * S) + E ε * V) (R₀ := E₀ * V) ?_ ?_ ?_
    · have := (hκ.smul_const (X * S)).add (tendsto_matrix_mul hE (tendsto_const_nhds (x := V)))
      simpa using this
    · rw [← Matrix.mul_assoc, hSG]
    · filter_upwards [hstep] with ε hs
      have h1 := hs.K_eq
      rw [smul_sub, sub_eq_iff_eq_add] at h1
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
      abel
  have hWL : M * (Xᵀ * G) = Xᵀ * E₀ := by
    have : M * (Xᵀ * G) = Xᵀ * (diagonal P.σt * (X * Xᵀ * G)) := by
      simp only [hM, Matrix.mul_assoc]
    rw [this, hPX, hSG]
  have hL : Tendsto (fun ε => (L' ε)ᵀ) (𝓝[>] 0) (𝓝 (Xᵀ * G)) := by
    refine tendsto_shifted M hdetM hκ
      (R := fun ε => (ε ^ 2 / (P.c * P.Δt)) • (S * Vᵀ) + Xᵀ * E ε) (R₀ := Xᵀ * E₀) ?_ hWL ?_
    · have := (hκ.smul_const (S * Vᵀ)).add (tendsto_matrix_mul (tendsto_const_nhds (x := Xᵀ)) hE)
      simpa using this
    · filter_upwards [hstep] with ε hs
      have h1 := congrArg Matrix.transpose hs.L_eq
      have hMt' : (Xᵀ * diagonal P.σt * X)ᵀ = M := hMt
      rw [transpose_smul, transpose_sub, transpose_sub, transpose_mul V, transpose_mul (L' ε) _,
        transpose_mul _ X, transpose_transpose, transpose_transpose, hMt', smul_sub,
        sub_eq_iff_eq_add] at h1
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
      abel
  have hS : Tendsto Sb (𝓝[>] 0) (𝓝 (Xᵀ * G * V)) := by
    refine tendsto_shifted M hdetM hκ
      (R := fun ε => (ε ^ 2 / (P.c * P.Δt)) • S + Xᵀ * E ε * V) (R₀ := Xᵀ * E₀ * V) ?_ ?_ ?_
    · have := (hκ.smul_const S).add (tendsto_matrix_mul
        (tendsto_matrix_mul (tendsto_const_nhds (x := Xᵀ)) hE) (tendsto_const_nhds (x := V)))
      simpa using this
    · rw [← Matrix.mul_assoc, hWL]
    · filter_upwards [hstep] with ε hs
      have h1 := hs.S_eq
      rw [smul_sub, sub_eq_iff_eq_add] at h1
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
      abel
  have hlim : Tendsto (fun ε => X * Sb ε * Vᵀ + (1 - X * Xᵀ) * (K' ε * Vᵀ)
      + X * (L' ε)ᵀ * (1 - V * Vᵀ)) (𝓝[>] 0)
      (𝓝 (X * (Xᵀ * G * V) * Vᵀ + (1 - X * Xᵀ) * (G * V * Vᵀ)
        + X * (Xᵀ * G) * (1 - V * Vᵀ))) :=
    ((tendsto_matrix_mul (tendsto_matrix_mul (tendsto_const_nhds (x := X)) hS)
      (tendsto_const_nhds (x := Vᵀ))).add
      (tendsto_matrix_mul (tendsto_const_nhds (x := 1 - X * Xᵀ))
        (tendsto_matrix_mul hK (tendsto_const_nhds (x := Vᵀ))))).add
      (tendsto_matrix_mul (tendsto_matrix_mul (tendsto_const_nhds (x := X)) hL)
        (tendsto_const_nhds (x := 1 - V * Vᵀ)))
  have a1 : X * (Xᵀ * G * V) * Vᵀ = G * V * Vᵀ := by
    calc X * (Xᵀ * G * V) * Vᵀ = (X * Xᵀ * G) * V * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPX]
  have a2 : (1 - X * Xᵀ) * (G * V * Vᵀ) = 0 := by
    have : X * Xᵀ * (G * V * Vᵀ) = (X * Xᵀ * G) * V * Vᵀ := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, this, hPX, sub_self]
  have a3 : X * (Xᵀ * G) * (1 - V * Vᵀ) = G - G * V * Vᵀ := by
    rw [← Matrix.mul_assoc X Xᵀ G, hPX, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  rw [a1, a2, a3, add_zero, add_sub_cancel] at hlim
  refine hlim.congr' ?_
  filter_upwards [hstep] with ε hs
  rw [augmented, matrix_parallelBUG_eq X (Xt ε) V (Vt ε) (Sb ε) (K' ε) (L' ε) hs.X_cap hs.V_cap]

/-- The limit of the truncated solution, under the property of the conservative truncation: `Y`
differs from `Ŷ = Û Ŝ V̂ᵀ` by at most the part of `Ŷ` outside the preserved directions `A`, `W`.
No lower bound on the rank of `Y` is involved. -/
theorem tendsto_truncated {σ₀ : ℝ} (hA : P.IsAdmissible σ₀) (hσ₀ : 0 < σ₀) {h T : C → ℝ}
    {X : Matrix F r ℝ} {S : Matrix r r ℝ} {V : Matrix ι r ℝ} {A : Matrix F p ℝ} {W : Matrix ι q ℝ}
    (hXV : P.Preserves T X V) (hAW : P.Preserves T A W)
    {K' Xt : ℝ → Matrix F r ℝ} {L' Vt : ℝ → Matrix ι r ℝ} {Sb : ℝ → Matrix r r ℝ}
    {Y : ℝ → Matrix F ι ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P.IsParallelStep ε h T X S V (K' ε) (L' ε) (Sb ε) (Xt ε) (Vt ε))
    (htr : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      frob2 (Y ε - augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε)) ≤
        frob2 (augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε)
          - A * Aᵀ * augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε) * (W * Wᵀ))) :
    Tendsto Y (𝓝[>] 0) (𝓝 (P.fluxMatrix T)) := by
  have hY := tendsto_augmented hA hσ₀ hXV hstep
  set Yh : ℝ → Matrix F ι ℝ := fun ε => augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε) with hYh
  have hN : Tendsto (fun ε => Yh ε - A * Aᵀ * Yh ε * (W * Wᵀ)) (𝓝[>] 0)
      (𝓝 (P.fluxMatrix T - A * Aᵀ * P.fluxMatrix T * (W * Wᵀ))) :=
    hY.sub (tendsto_matrix_mul (tendsto_matrix_mul (tendsto_const_nhds (x := A * Aᵀ)) hY)
      (tendsto_const_nhds (x := W * Wᵀ)))
  rw [hAW.left_fix, hAW.right_fix, sub_self] at hN
  have hcf : Continuous (frob2 : Matrix F ι ℝ → ℝ) := by
    unfold frob2
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_id.matrix_elem i j).pow 2
  have hf0 : Tendsto (fun ε => √(frob2 (Yh ε - A * Aᵀ * Yh ε * (W * Wᵀ)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ((Real.continuous_sqrt.comp hcf).tendsto (0 : Matrix F ι ℝ)).comp hN
    have h2 : ((fun x => √x) ∘ frob2) (0 : Matrix F ι ℝ) = 0 := by simp [frob2]
    rw [h2] at h1
    exact h1
  have hentry : ∀ f ℓ, Tendsto (fun ε => (Y ε - Yh ε) f ℓ) (𝓝[>] 0) (𝓝 0) := fun f ℓ => by
    refine squeeze_zero_norm' ?_ hf0
    filter_upwards [htr] with ε hε
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt (le_trans ?_ hε)
    have h1 : (Y ε - Yh ε) f ℓ ^ 2 ≤ ∑ j, (Y ε - Yh ε) f j ^ 2 :=
      Finset.single_le_sum (f := fun j => (Y ε - Yh ε) f j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ ℓ)
    have h2 : ∑ j, (Y ε - Yh ε) f j ^ 2 ≤ ∑ i, ∑ j, (Y ε - Yh ε) i j ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j, (Y ε - Yh ε) i j ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ f)
    exact h1.trans h2
  refine tendsto_pi_nhds.2 fun f => tendsto_pi_nhds.2 fun ℓ => ?_
  have h1 := (hentry f ℓ).add (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hY f) ℓ)
  simpa using h1

/-- **Theorem 5 of arXiv 2502.20883** (asymptotic preservation of the macro–micro parallel BUG
scheme).  Let `X`, `V` be pre-augmented by `(Σᵗ)⁻¹ 𝐝⁰_v B(Tⁿ)` and `Q_v 𝟙` (`hXV`), let `K'`, `L'`,
`S̄` solve (4.2)–(4.4) with any augmentation of the bases, let `Y` be a conservative truncation of
the augmented solution, preserving the directions `A`, `W` (`htr`, `hAW`), and let `h'`, `T'` be
updated by (3.3b), (3.3c) with `g^{n+1} = Y`.  Then, as `ε → 0` for fixed data at time `tₙ`,
`g^{n+1} → -(Σᵗ)⁻¹ (𝐝⁰_x B 𝟙ᵀ Q_x + 𝐝⁰_y B 𝟙ᵀ Q_y)`, and `T^{n+1}` converges to a solution of the
discrete Rosseland equation.

Differences from the paper: the limit is an actual limit, and the full rank of `Xᵀ Σᵗ X` is derived.
The conservative truncation is not spelled out in the paper; the hypothesis `htr` is a property
that the truncations of its references share, since they keep `Ŷ W Wᵀ` (`A = 1`, see
`conservative_right`) or `A Aᵀ Ŷ` and modify the complement by a best approximation.  The `V` part
of `hXV` is not needed: the pre-augmentation of `V` matters through `W` only. -/
theorem theorem_5 [Fintype C] {σ₀ : ℝ} (hQ2 : P.IsSecondOrder) (hA : P.IsAdmissible σ₀)
    (hσ₀ : 0 < σ₀) (hσa : ∀ z, 0 < P.σa z) {h T : C → ℝ}
    {X : Matrix F r ℝ} {S : Matrix r r ℝ} {V : Matrix ι r ℝ} {A : Matrix F p ℝ} {W : Matrix ι q ℝ}
    (hXV : P.Preserves T X V) (hAW : P.Preserves T A W)
    {K' Xt : ℝ → Matrix F r ℝ} {L' Vt : ℝ → Matrix ι r ℝ} {Sb : ℝ → Matrix r r ℝ}
    {Y : ℝ → Matrix F ι ℝ} {h' T' : ℝ → C → ℝ}
    (hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P.IsParallelStep ε h T X S V (K' ε) (L' ε) (Sb ε) (Xt ε) (Vt ε))
    (htr : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      frob2 (Y ε - augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε)) ≤
        frob2 (augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε)
          - A * Aᵀ * augmented X (Xt ε) V (Vt ε) (K' ε) (L' ε) (Sb ε) * (W * Wᵀ)))
    (hmacro : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      P.IsMacroStep ε h T (fun f ℓ => Y ε f ℓ) (h' ε) (T' ε))
    (hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z, 0 ≤ T' ε z) :
    Tendsto Y (𝓝[>] 0) (𝓝 (P.fluxMatrix T)) ∧
      ∃ T₁ : C → ℝ, Tendsto T' (𝓝[>] 0) (𝓝 T₁) ∧ (∀ z, 0 ≤ T₁ z) ∧ P.IsRosseland T T₁ := by
  have hlim := tendsto_truncated hA hσ₀ hXV hAW hstep htr
  refine ⟨hlim, ?_⟩
  obtain ⟨T₁, h₁, h1, -, h3, h4⟩ := macro_limit (g' := fun ε f ℓ => Y ε f ℓ) (G := P.limitFlux T)
    hA hσa hmacro hlim (tendsto_const_nhds (x := h)) (tendsto_const_nhds (x := T)) hpos
  refine ⟨T₁, h1, h3, fun z => ?_⟩
  rw [h4 z, wQD_limitFlux hQ2, neg_neg]

/-- The conservative truncation of the references [16, 17] of arXiv 2502.20883 satisfies the
hypothesis of `theorem_5` with `A = 1`: the part `Ŷ W Wᵀ` of `Ŷ` along the preserved angular vectors
is kept and only the remainder is replaced, by something at least as close as `0` (for instance a
truncated singular value decomposition). -/
theorem conservative_right {Yh Z : Matrix F ι ℝ} {W : Matrix ι q ℝ}
    (hZ : frob2 (Z - Yh * (1 - W * Wᵀ)) ≤ frob2 (Yh * (1 - W * Wᵀ))) :
    frob2 (Yh * (W * Wᵀ) + Z - Yh) ≤
      frob2 (Yh - (1 : Matrix F F ℝ) * (1 : Matrix F F ℝ)ᵀ * Yh * (W * Wᵀ)) := by
  have e1 : Yh * (W * Wᵀ) + Z - Yh = Z - Yh * (1 - W * Wᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  have e2 : Yh - (1 : Matrix F F ℝ) * (1 : Matrix F F ℝ)ᵀ * Yh * (W * Wᵀ) =
      Yh * (1 - W * Wᵀ) := by
    rw [transpose_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  rw [e1, e2]
  exact hZ

end Setup

end LowRank

/-! ### Non-vacuity -/

section NonVacuous

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- The macro equations can be solved, with `T' ≥ 0`, as soon as the right-hand side of the scalar
equation for `T'` is nonnegative. -/
theorem exists_isMacroStep {σ₀ ε : ℝ} (hA : P.IsAdmissible σ₀) (hσa : ∀ z, 0 < P.σa z)
    (g' : F → ι → ℝ) (h T : C → ℝ)
    (hρ : ∀ z, 0 ≤ P.cν / P.Δt * (1 + ε ^ 2 / (P.c * P.σa z * P.Δt)) * T z
      + P.a / P.Δt * T z ^ 4 + 2 * π * ε ^ 2 / (P.c * P.Δt) * h z
      - (P.wQD P.x P.Ωx g' z + P.wQD P.y P.Ωy g' z)) :
    ∃ h' T' : C → ℝ, P.IsMacroStep ε h T g' h' T' ∧ ∀ z, 0 ≤ T' z := by
  have hπ := Real.pi_pos
  have hc := hA.c_pos
  have hcν := hA.cν_pos
  have hΔt := hA.Δt_pos
  have ha := hA.a_nonneg
  have cell : ∀ z, ∃ x, 0 ≤ x ∧
      P.cν / P.Δt * (1 + ε ^ 2 / (P.c * P.σa z * P.Δt)) * x + P.a / P.Δt * x ^ 4 =
      P.cν / P.Δt * (1 + ε ^ 2 / (P.c * P.σa z * P.Δt)) * T z
      + P.a / P.Δt * T z ^ 4 + 2 * π * ε ^ 2 / (P.c * P.Δt) * h z
      - (P.wQD P.x P.Ωx g' z + P.wQD P.y P.Ωy g' z) := fun z => by
    have hσ := hσa z
    exact exists_root (by positivity) (by positivity) (hρ z)
  choose x hx0 hx using cell
  refine ⟨fun z => P.cν / P.Δt * (x z - T z) / (2 * π * P.σa z), x, ⟨fun z => ?_, fun z => ?_⟩, hx0⟩
  · have hσ := hσa z
    have e := hx z
    simp only [B]
    linear_combination (norm := (field_simp; ring)) (1 / (2 * π)) * e
  · have hσ := hσa z
    field_simp

/-- The scheme can be solved on a grid without boundary faces: `g'` is given by an explicit formula
and `h'`, `T'` by `exists_isMacroStep`. -/
theorem exists_isStep {σ₀ ε : ℝ} (hA : P.IsAdmissible σ₀) (hσ₀ : 0 < σ₀) (hσa : ∀ z, 0 < P.σa z)
    (hε : 0 < ε) (hper : ∀ f, P.Inner f) (g : F → ι → ℝ) (h T : C → ℝ) :
    ∃ g' : F → ι → ℝ, (∀ f ℓ, P.MicroEq ε g h T g' f ℓ) ∧
      ((∀ z, 0 ≤ P.cν / P.Δt * (1 + ε ^ 2 / (P.c * P.σa z * P.Δt)) * T z
        + P.a / P.Δt * T z ^ 4 + 2 * π * ε ^ 2 / (P.c * P.Δt) * h z
        - (P.wQD P.x P.Ωx g' z + P.wQD P.y P.Ωy g' z)) →
      ∃ h' T' : C → ℝ, P.IsStep ε g h T g' h' T' ∧ ∀ z, 0 ≤ T' z) := by
  have hc := hA.c_pos
  have hΔt := hA.Δt_pos
  have hσ : ∀ f, 0 < P.σt f := fun f => hσ₀.trans_le (hA.σ₀_le f)
  have hne : ∀ f, ε ^ 2 / (P.c * P.Δt) + P.σt f ≠ 0 := fun f => by
    have := hσ f
    positivity
  set g' : F → ι → ℝ := fun f ℓ => (ε ^ 2 / (P.c * P.Δt) * g f ℓ
    - ε * P.meanFree (P.transport g f) ℓ - P.Ωx ℓ * P.x.δ (P.phi ε h T) f
    - P.Ωy ℓ * P.y.δ (P.phi ε h T) f) / (ε ^ 2 / (P.c * P.Δt) + P.σt f) with hg'
  have hm : ∀ f ℓ, P.MicroEq ε g h T g' f ℓ := fun f ℓ => by
    have e : g' f ℓ * (ε ^ 2 / (P.c * P.Δt) + P.σt f) = ε ^ 2 / (P.c * P.Δt) * g f ℓ
        - ε * P.meanFree (P.transport g f) ℓ - P.Ωx ℓ * P.x.δ (P.phi ε h T) f
        - P.Ωy ℓ * P.y.δ (P.phi ε h T) f := by
      simp only [hg']
      rw [div_mul_cancel₀ _ (hne f)]
    rw [MicroEq]
    linear_combination e
  refine ⟨g', hm, fun hρ => ?_⟩
  obtain ⟨h', T', h1, h2⟩ := exists_isMacroStep hA hσa g' h T hρ
  exact ⟨h', T', ⟨h1, fun f _ ℓ => hm f ℓ, fun f hf => absurd (hper f) hf⟩, h2⟩

end Setup

/-- With zero boundary conditions: the direction of a grid of `n + 1` cell nodes between `n + 2`
faces.  Exactly the two boundary faces are not inner (`zeroStencil_isInner_iff`), so that the
boundary hypothesis of `theorem_1_mass` and `theorem_3` is `g = 0` on these faces. -/
def zeroStencil (n : ℕ) (Δ : ℝ) : Stencil (Fin (n + 1)) (Fin (n + 2)) where
  right c := c.succ
  left c := c.castSucc
  ahead f := ⟨min f.1 n, by omega⟩
  behind f := ⟨f.1 - 1, by omega⟩
  ahead_left c := by
    ext
    simp only [Fin.val_castSucc]
    omega
  behind_right c := by
    ext
    simp
  Δ := Δ

/-- The faces of `zeroStencil` that are not inner are the two boundary faces. -/
theorem zeroStencil_isInner_iff (n : ℕ) (Δ : ℝ) (f : Fin (n + 2)) :
    (zeroStencil n Δ).IsInner f ↔ f.1 ≠ 0 ∧ f.1 ≠ n + 1 := by
  simp only [Stencil.IsInner, zeroStencil, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

/-- The setup of the first example: the periodic grid with unit mesh, the order-two product rule,
unit constants and `Δt = 1/12`, which satisfies the CFL condition for all `ε ≥ 0`. -/
def s2Setup (Nx Ny : ℕ) : Setup (Node Nx Ny) (Node Nx Ny) (Bool × Bool) where
  x := periodicX Nx Ny 1
  y := periodicY Nx Ny 1
  c := 1
  cν := 1
  a := 1
  Δt := 1 / 12
  w := s2w
  Ωx := s2x
  Ωy := s2y
  σt := fun _ => 1
  σa := fun _ => 1

/-- The points of the order-two product rule lie in the unit square. -/
theorem abs_s2x_le (b : Bool × Bool) : |s2x b| ≤ 1 := by
  have h0 : (0 : ℝ) < √3 := by positivity
  rw [s2x, abs_div, abs_of_pos h0, div_le_one h0]
  split_ifs <;> simp

/-- The points of the order-two product rule lie in the unit square. -/
theorem abs_s2y_le (b : Bool × Bool) : |s2y b| ≤ 1 := by
  have h0 : (0 : ℝ) < √3 := by positivity
  rw [s2y, abs_div, abs_of_pos h0, div_le_one h0]
  split_ifs <;> simp

/-- The rule of the first example satisfies `IsQuadrature`. -/
theorem s2Setup_isQuadrature (Nx Ny : ℕ) : (s2Setup Nx Ny).IsQuadrature where
  w_nonneg _ := by
    simp only [s2Setup, s2w]
    positivity
  sum_w := s2_moments.1
  sum_Ωx := s2_moments.2.1
  sum_Ωy := s2_moments.2.2.1
  abs_Ωx_le := abs_s2x_le
  abs_Ωy_le := abs_s2y_le

/-- The rule of the first example satisfies `IsSecondOrder`. -/
theorem s2Setup_isSecondOrder (Nx Ny : ℕ) : (s2Setup Nx Ny).IsSecondOrder :=
  ⟨s2_moments.2.2.2.1, s2_moments.2.2.2.2.1, s2_moments.2.2.2.2.2⟩

/-- The data of the first example are admissible. -/
theorem s2Setup_isAdmissible (Nx Ny : ℕ) : (s2Setup Nx Ny).IsAdmissible 1 where
  c_pos := by simp [s2Setup]
  cν_pos := by simp [s2Setup]
  a_nonneg := by simp [s2Setup]
  Δt_pos := by simp [s2Setup]
  Δx_pos := by simp [s2Setup, periodicX]
  Δy_pos := by simp [s2Setup, periodicY]
  σ₀_nonneg := zero_le_one
  σ₀_le _ := le_refl _
  σa_nonneg _ := zero_le_one

/-- The CFL condition (3.9) holds in the first example for all `ε ≥ 0`. -/
theorem s2Setup_cfl (Nx Ny : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : (s2Setup Nx Ny).CFL ε 1 := by
  have key : ∀ t : ℝ, |t| ≤ 1 → t ≠ 0 →
      (1 : ℝ) / 12 ≤ 1 / (3 * 1) * (ε * 1 + 1 * 1 ^ 2 / (4 * |t|)) := by
    intro t ht ht0
    have h0 : 0 < |t| := abs_pos.2 ht0
    have h1 : 1 / 4 ≤ 1 * 1 ^ 2 / (4 * |t|) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have e : 1 / (3 * 1) * (ε * 1 + 1 * 1 ^ 2 / (4 * |t|)) = (ε + 1 * 1 ^ 2 / (4 * |t|)) / 3 := by
      ring
    rw [e]
    linarith
  exact ⟨fun ℓ h => key _ (abs_s2x_le ℓ) h, fun ℓ h => key _ (abs_s2y_le ℓ) h⟩

/-- All hypotheses of `theorem_3` and `theorem_2_step` hold together, for every `ε > 0` and on every
periodic grid, with a nonzero flux: a spatially constant flux of zero mean decays by the factor
`12 ε² / (12 ε² + 1)` while `h = 0` and `T = 1` do not change.  The step size does not depend on
`ε`, which is the point of the mixed CFL condition. -/
theorem theorem_3_nonvacuous (Nx Ny : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (s2Setup Nx Ny).IsStep ε (fun _ ℓ => s2x ℓ) (fun _ => 0) (fun _ => 1)
      (fun _ ℓ => 12 * ε ^ 2 / (12 * ε ^ 2 + 1) * s2x ℓ) (fun _ => 0) (fun _ => 1) ∧
    (s2Setup Nx Ny).CFL ε 1 ∧ ∑ ℓ, (s2Setup Nx Ny).w ℓ * s2x ℓ = 0 := by
  refine ⟨⟨⟨fun z => ?_, fun z => ?_⟩, fun f _ ℓ => ?_,
    fun f hf => absurd (periodic_inner Nx Ny 1 1 f) hf⟩, s2Setup_cfl Nx Ny hε.le,
    s2_moments.2.1⟩
  · simp [Setup.wQD, Stencil.D0]
  · simp
  · have hT : (s2Setup Nx Ny).transport (fun _ ℓ => s2x ℓ) f = fun _ => 0 := by
      funext ℓ
      simp [Setup.transport, Stencil.upwind, Stencil.Dp, Stencil.Dm]
    rw [Setup.MicroEq, hT]
    simp only [Setup.meanFree, Stencil.δ, Setup.phi]
    simp only [s2Setup, mul_zero, Finset.sum_const_zero, sub_self, zero_div]
    have : 12 * ε ^ 2 + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- `theorem_3` applies to the first example. -/
example (Nx Ny : ℕ) [NeZero Nx] [NeZero Ny] {ε : ℝ} (hε : 0 < ε) :
    (s2Setup Nx Ny).energy ε (fun _ ℓ => 12 * ε ^ 2 / (12 * ε ^ 2 + 1) * s2x ℓ) (fun _ => 0)
      (fun _ => 1) ≤ (s2Setup Nx Ny).energy ε (fun _ ℓ => s2x ℓ) (fun _ => 0) (fun _ => 1) :=
  Setup.theorem_3 (s2Setup_isQuadrature _ _) (s2Setup_isSecondOrder _ _) (s2Setup_isAdmissible _ _)
    hε (s2Setup_cfl _ _ hε.le) (theorem_3_nonvacuous Nx Ny hε).1
    (fun f hf => absurd (periodic_inner Nx Ny 1 1 f) hf) (fun _ => s2_moments.2.1)
    (fun _ => zero_le_one) (fun _ => zero_le_one)

/-- `theorem_2_step` applies to the first example. -/
example (Nx Ny : ℕ) [NeZero Nx] [NeZero Ny] :
    Tendsto (fun (ε : ℝ) (_ : Node Nx Ny) ℓ => 12 * ε ^ 2 / (12 * ε ^ 2 + 1) * s2x ℓ) (𝓝[>] 0)
      (𝓝 ((s2Setup Nx Ny).limitFlux fun _ => 1)) :=
  (Setup.theorem_2_step (s2Setup_isSecondOrder Nx Ny) (s2Setup_isAdmissible Nx Ny) one_pos
    (fun _ => one_pos) (fun f => periodic_inner Nx Ny 1 1 f)
    (g := fun _ _ ℓ => s2x ℓ) (h := fun _ _ => 0) (T := fun _ _ => 1) (h' := fun _ _ => 0)
    (T' := fun _ _ => 1)
    (eventually_mem_nhdsWithin.mono fun _ hε => (theorem_3_nonvacuous Nx Ny hε).1)
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
    (Eventually.of_forall fun _ _ => zero_le_one)).1

namespace Setup

variable {P : Setup C F ι} [Fintype ι] {r : Type*} [Fintype r] [DecidableEq r] [Fintype F]
  [DecidableEq F] [DecidableEq ι]

open Matrix

omit [Fintype ι] [Fintype r] [DecidableEq r] [Fintype F] [DecidableEq F] [DecidableEq ι] in
/-- If `(κ + σ) d = 1` then `Z' = d Z` solves `κ Z' = Z - σ Z'`. -/
theorem smul_solve {a b : Type*} {κ σ d : ℝ} (hd : (κ + σ) * d = 1) (Z : Matrix a b ℝ) :
    κ • (d • Z) = Z - σ • (d • Z) := by
  have h1 : (κ + σ) • (d • Z) = Z := by rw [smul_smul, hd, one_smul]
  rw [add_smul] at h1
  exact eq_sub_of_add_eq h1

/-- `rhs` at `Y = 0`, `h = 0` does not depend on `ε`. -/
theorem rhs_zero (ε : ℝ) (T : C → ℝ) : P.rhs ε (0 : Matrix F ι ℝ) (fun _ => 0) T =
    Matrix.of fun f ℓ =>
      -(P.Ωx ℓ * P.x.δ (fun z => P.B (T z)) f + P.Ωy ℓ * P.y.δ (fun z => P.B (T z)) f) := by
  have h1 : P.phi ε (fun _ => 0) T = fun z => P.B (T z) := by
    funext z
    simp [phi]
  have h2 : ∀ f, P.transport (0 : Matrix F ι ℝ) f = fun _ => 0 := fun f => by
    funext ℓ
    simp [transport, Stencil.upwind, Stencil.Dp, Stencil.Dm]
  ext f ℓ
  simp [rhs, h1, h2, meanFree]

/-- The K-, L- and S-steps can be solved and the augmentation is possible, in the case of a constant
cross section, `S = 0` and `h = 0`, when `X` and `V` are pre-augmented: then `X̃ = Ṽ = 0` do. -/
theorem exists_isParallelStep {σ ε : ℝ} (hσ : ∀ f, P.σt f = σ) (hσ0 : 0 < σ)
    (hκ : 0 < ε ^ 2 / (P.c * P.Δt)) {T : C → ℝ} {X : Matrix F r ℝ} {V : Matrix ι r ℝ}
    (hXV : P.Preserves T X V) :
    ∃ (K' : Matrix F r ℝ) (L' : Matrix ι r ℝ) (Sb : Matrix r r ℝ),
      P.IsParallelStep ε (fun _ => 0) T X 0 V K' L' Sb 0 0 := by
  set κ := ε ^ 2 / (P.c * P.Δt) with hκdef
  have hSig : (diagonal P.σt : Matrix F F ℝ) = σ • 1 := by
    ext f f'
    by_cases hf : f = f'
    · subst hf
      simp [hσ]
    · simp [hf]
  set E : Matrix F ι ℝ := P.rhs ε (0 : Matrix F ι ℝ) (fun _ => 0) T with hE
  have hE0 : X * (0 : Matrix r r ℝ) * Vᵀ = 0 := by simp
  have hEG : E = σ • P.fluxMatrix T := by
    rw [hE, rhs_zero, ← diagonal_mul_fluxMatrix (fun f => by rw [hσ]; exact hσ0.ne'), hSig,
      Matrix.smul_mul, Matrix.one_mul]
  have hPE : X * Xᵀ * E = E := by
    rw [hEG, Matrix.mul_smul, hXV.left_fix]
  have hEP : E * (V * Vᵀ) = E := by
    rw [hEG, Matrix.smul_mul, hXV.right_fix]
  have hEP' : V * Vᵀ * Eᵀ = Eᵀ := by
    have := congrArg Matrix.transpose hEP
    simpa only [transpose_mul, transpose_transpose] using this
  set d := (κ + σ)⁻¹ with hd
  have hd1 : (κ + σ) * d = 1 := mul_inv_cancel₀ (by positivity)
  have hM : Xᵀ * diagonal P.σt * X = σ • 1 := by
    rw [hSig, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hXV.A_orth]
  refine ⟨d • (E * V), d • (Eᵀ * X), d • (Xᵀ * E * V), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hE0, Matrix.mul_zero, sub_zero, hSig, Matrix.smul_mul, Matrix.one_mul]
    exact smul_solve hd1 _
  · rw [hE0, transpose_zero, Matrix.mul_zero, sub_zero, hM, Matrix.mul_smul, Matrix.mul_one]
    exact smul_solve hd1 _
  · rw [hE0, sub_zero, hM, Matrix.smul_mul, Matrix.one_mul]
    exact smul_solve hd1 _
  · rw [matrix_augmented_proj, transpose_zero, Matrix.mul_zero, add_zero, Matrix.mul_smul,
      ← Matrix.mul_assoc, hPE]
  · rw [matrix_augmented_proj, transpose_zero, Matrix.mul_zero, add_zero, Matrix.mul_smul,
      ← Matrix.mul_assoc, hEP']

end Setup

/-- The direction `x` of the second example: two cell nodes and two faces on a circle. -/
def miniX : Stencil Bool Bool where
  right c := c
  left c := !c
  ahead f := !f
  behind f := f
  ahead_left c := by simp
  behind_right _ := rfl
  Δ := 1

/-- The direction `y` of the second example, in which nothing varies. -/
def miniY : Stencil Bool Bool where
  right c := c
  left c := c
  ahead f := f
  behind f := f
  ahead_left _ := rfl
  behind_right _ := rfl
  Δ := 1

/-- The setup of the second example. -/
def miniSetup : Setup Bool Bool (Bool × Bool) where
  x := miniX
  y := miniY
  c := 1
  cν := 1
  a := 1
  Δt := 1
  w := s2w
  Ωx := s2x
  Ωy := s2y
  σt := fun _ => 1
  σa := fun _ => 1

/-- The temperature of the second example, which is not constant. -/
def miniT (z : Bool) : ℝ := if z then 1 else 0

/-- The orthonormal basis of `span(Q_x 𝟙, Q_y 𝟙)`. -/
def miniV : Matrix (Bool × Bool) Bool ℝ :=
  Matrix.of fun ℓ j => √3 / 2 * (if j then s2x ℓ else s2y ℓ)

/-- `miniV` has orthonormal columns. -/
theorem miniV_orth : miniVᵀ * miniV = 1 := by
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  have h := s2_sqrt
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, miniV, Matrix.of_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, s2x, s2y, ite_true, ite_false, Bool.false_eq_true,
      Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, not_false_eq_true,
      Bool.true_eq_false] <;> field_simp <;> nlinarith [h]

/-- The hypotheses of `theorem_5` on the pre-augmentation and on the parallel update hold together
for every `ε > 0` with a nonzero limit flux: a nonconstant temperature on two cell nodes, the
order-two product rule, `X = 1` and `V` the orthonormal basis of `span(Q_x 𝟙, Q_y 𝟙)`. -/
theorem theorem_5_nonvacuous :
    miniSetup.Preserves miniT (1 : Matrix Bool Bool ℝ) miniV ∧ miniSetup.fluxMatrix miniT ≠ 0 ∧
      miniSetup.IsSecondOrder ∧ miniSetup.IsAdmissible 1 ∧ ∀ ε : ℝ, 0 < ε →
        ∃ (K' : Matrix Bool Bool ℝ) (L' : Matrix (Bool × Bool) Bool ℝ) (Sb : Matrix Bool Bool ℝ),
          miniSetup.IsParallelStep ε (fun _ => 0) miniT 1 0 miniV K' L' Sb 0 0 := by
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  have hpre : miniSetup.Preserves miniT (1 : Matrix Bool Bool ℝ) miniV := by
    refine ⟨by simp, miniV_orth, ⟨_, (Matrix.one_mulVec _).symm⟩, ⟨_, (Matrix.one_mulVec _).symm⟩,
      ⟨fun j => if j then 2 / √3 else 0, ?_⟩, ⟨fun j => if j then 0 else 2 / √3, ?_⟩⟩
    · funext ℓ
      simp only [miniSetup, Matrix.mulVec, dotProduct, miniV, Matrix.of_apply, Fintype.sum_bool,
        ite_true, ite_false, Bool.false_eq_true]
      field_simp
      ring
    · funext ℓ
      simp only [miniSetup, Matrix.mulVec, dotProduct, miniV, Matrix.of_apply, Fintype.sum_bool,
        ite_true, ite_false, Bool.false_eq_true]
      field_simp
      ring
  refine ⟨hpre, ?_, ⟨s2_moments.2.2.2.1, s2_moments.2.2.2.2.1, s2_moments.2.2.2.2.2⟩, ?_, ?_⟩
  · intro h
    have h1 := congrFun (congrFun h false) (true, true)
    simp only [Setup.fluxMatrix, Setup.limitFlux, Matrix.of_apply, Matrix.zero_apply, miniSetup,
      miniX, miniY, Stencil.δ, Setup.B, miniT, s2x, s2y, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true] at h1
    have hπ := Real.pi_ne_zero
    field_simp at h1
    norm_num at h1
  · exact ⟨by simp [miniSetup], by simp [miniSetup], by simp [miniSetup], by simp [miniSetup],
      by simp [miniSetup, miniX], by simp [miniSetup, miniY], zero_le_one, fun _ => le_refl _,
      fun _ => zero_le_one⟩
  · intro ε hε
    refine Setup.exists_isParallelStep (σ := 1) (fun _ => rfl) one_pos ?_ hpre
    simp only [miniSetup]
    positivity

end NonVacuous

/-! ### The quadrature in the core kinetic vocabulary -/

section KineticCore

namespace Setup

variable {P : Setup C F ι} [Fintype ι]

/-- **The quadrature as a core quadrature**: a rule with `IsQuadrature` and positive weights gives
a core `Kinetic.Quadrature` for the first components of its points: nodes `Ω_x`, weights
`w_ℓ / (2π)`.  The rule of this file has total mass `2π`, the core one has total mass one; the core
asks for positive weights and `IsQuadrature` for nonnegative ones, hence the hypothesis `hw`. -/
def IsQuadrature.toQuadratureX (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    Kinetic.Quadrature ι where
  μ := P.Ωx
  w := fun ℓ => P.w ℓ / (2 * π)
  w_pos := fun ℓ => div_pos (hw ℓ) (by positivity)
  sum_w := by rw [← Finset.sum_div, hQ.sum_w, div_self (by positivity)]

/-- The same for the second components `Ω_y` of the points. -/
def IsQuadrature.toQuadratureY (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    Kinetic.Quadrature ι where
  μ := P.Ωy
  w := fun ℓ => P.w ℓ / (2 * π)
  w_pos := fun ℓ => div_pos (hw ℓ) (by positivity)
  sum_w := by rw [← Finset.sum_div, hQ.sum_w, div_self (by positivity)]

@[simp]
theorem IsQuadrature.toQuadratureX_μ (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    (hQ.toQuadratureX hw).μ = P.Ωx := rfl

@[simp]
theorem IsQuadrature.toQuadratureY_μ (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    (hQ.toQuadratureY hw).μ = P.Ωy := rfl

@[simp]
theorem IsQuadrature.toQuadratureX_w (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    (hQ.toQuadratureX hw).w = fun ℓ => P.w ℓ / (2 * π) := rfl

@[simp]
theorem IsQuadrature.toQuadratureY_w (hQ : P.IsQuadrature) (hw : ∀ ℓ, 0 < P.w ℓ) :
    (hQ.toQuadratureY hw).w = fun ℓ => P.w ℓ / (2 * π) := rfl

end Setup

/-- The weights `π / 2` of the order-two product rule are positive. -/
theorem s2Setup_w_pos (Nx Ny : ℕ) (ℓ : Bool × Bool) : 0 < (s2Setup Nx Ny).w ℓ := by
  simp only [s2Setup, s2w]
  positivity

/-- The bridge at the order-two product rule of the first example. -/
example : ((s2Setup_isQuadrature 3 3).toQuadratureX (s2Setup_w_pos 3 3)).μ = s2x ∧
    ((s2Setup_isQuadrature 3 3).toQuadratureY (s2Setup_w_pos 3 3)).μ = s2y :=
  ⟨rfl, rfl⟩

end KineticCore

end

end LeanDLRA.Literature.P2502_20883

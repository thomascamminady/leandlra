import LeanDLRA.Literature.Kinetic.P2106_09445a
import LeanDLRA.Stability.Conservation

/-!
# Structure-preserving collision DeepONets (arXiv 2402.16613)

Lee, Schotthöfer, Xiao, Krumscheid and Frank, *Structure-Preserving Operator Learning: Modeling
the Collision Operator of Kinetic Equations* (arXiv 2402.16613).  The paper approximates the
linear collision operator `Q` by a DeepONet `Q_θ(f)(v) = ∑_{k ≤ p+1} β_k(f̄) τ_k(v)` (Eq. (8)) on
the sensor points `v₁, …, v_m`, which coincide with the quadrature points of the kinetic solver
(Section 4.1), and enforces the collision invariant `⟨φ Q_θ(f)⟩ = 0` (Eq. (3), `φ = 1`: mass)
by construction.  Its mathematical statements are the one-line proofs that the two
constructions preserve the invariant (Eq. (10) and the display after it), the mass rescaling
(15), the normalization of the first multiplier in the entropy-based sampling (Algorithm 3), and
the remark that the hybrid system (17) then conserves mass.  Everything else is empirical.

This module states these on the velocity quadrature of `P2106_09445a` (`avg`), and connects the
conservation property to the core: a collision DeepONet with the invariant gives a field whose
explicit Euler steps, and explicit Euler Galerkin (low-rank) steps whose projector contains the
invariant direction, conserve the mass `⟪w φ, f⟫` (core `eulerStep`, `galerkinEulerStep`,
`galerkinEulerStep_inner_eq`, `inner_eq_of_forall_step`).

## Main results

* `deepONet_preserves_of_orthogonal` (**Method I**, Eq. (10)): trunk functions orthogonal to the
  collision invariant `φ = τ_{p+1}` (Eq. (9)) and `β_{p+1} = 0` give `⟨φ Q_θ(f)⟩ = 0`.
* `deepONet_preserves_biasAdapted` (**Method II**): `τ_{p+1} = 1` and
  `β_{p+1} = -∑_k β_k ⟨φ τ_k⟩ / ⟨φ⟩` give `⟨φ Q_θ(f)⟩ = 0`.
* `massRescale_preserves` (Eq. (15)): `f ↦ ⟨f⟩ Q_θ(f / ⟨f⟩)` keeps the invariant.
* `samplingMultiplier_mass_eq_one` (Algorithm 3): `α₁ = -(log m₁ + log ⟨exp(α_# · m_#)⟩)/m₁`
  gives unit mass, via `zerothMoment_eq_one_iff`.
* `mass_eulerStep_eq`, `mass_eulerStep_iter_eq`, `mass_galerkinEulerStep_eq`: conservation of mass
  for the collision part of the hybrid system (17) under explicit Euler, iterated, and for
  projected (low-rank Galerkin) Euler steps.

Differences from the paper: the velocity integral is the quadrature on the sensor points (as in
the paper's solver); the hybrid system (17) is treated through its collision part
`∂ₜ f = σ_s Q_θ(f)` with explicit Euler steps (the transport part is not modelled).  No claim of
the paper was found to be false.
-/

open Finset
open scoped Matrix RealInnerProductSpace

namespace LeanDLRA.Literature.P2402_16613

open LeanDLRA LeanDLRA.Literature.P2106_09445

variable {V : Type*} [Fintype V] {p : ℕ}

/-- The **collision DeepONet** (Eq. (8)): `Q_θ(f)(v) = ∑_{k=1}^{p+1} β_k(f) τ_k(v)` with branch net
`β` (acting on the sensor values) and trunk net `τ`. -/
def deepONet (β : (V → ℝ) → Fin (p + 1) → ℝ) (τ : Fin (p + 1) → V → ℝ) (f : V → ℝ) : V → ℝ :=
  fun v => ∑ k, β f k * τ k v

/-- An operator `Q` **has the collision invariant** `φ`: `⟨φ Q(f)⟩ = 0` for all `f` (Eq. (3)). -/
def HasInvariant (w φ : V → ℝ) (Q : (V → ℝ) → V → ℝ) : Prop :=
  ∀ f, avg w (fun v => φ v * Q f v) = 0

/-- The invariant of a DeepONet output is the branch-weighted sum of the trunk invariants. -/
lemma avg_deepONet (w φ : V → ℝ) (β : (V → ℝ) → Fin (p + 1) → ℝ) (τ : Fin (p + 1) → V → ℝ)
    (f : V → ℝ) :
    avg w (fun v => φ v * deepONet β τ f v) = ∑ k, β f k * avg w (fun v => φ v * τ k v) := by
  simp only [avg, deepONet, mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun v _ => by ring

/-- **Method I** (Eq. (10)): if the last trunk function is the collision invariant,
`τ_{p+1} = φ`, with fixed coefficient `β_{p+1} = 0`, and the other trunk functions are orthogonal
to it, `⟨τ_k τ_{p+1}⟩ = 0` (part of Eq. (9)), the DeepONet preserves the invariant. -/
theorem deepONet_preserves_of_orthogonal (w φ : V → ℝ) (β : (V → ℝ) → Fin (p + 1) → ℝ)
    (τ : Fin (p + 1) → V → ℝ) (hlast : τ (Fin.last p) = φ) (hβ : ∀ f, β f (Fin.last p) = 0)
    (horth : ∀ k : Fin p, avg w (fun v => τ k.castSucc v * τ (Fin.last p) v) = 0) :
    HasInvariant w φ (deepONet β τ) := by
  intro f
  rw [avg_deepONet, Fin.sum_univ_castSucc, hβ, zero_mul, add_zero]
  refine sum_eq_zero fun k _ => ?_
  have h' : avg w (fun v => φ v * τ k.castSucc v) = 0 := by
    have := horth k
    rw [hlast] at this
    rw [← this]
    exact sum_congr rfl fun v _ => by ring
  rw [h', mul_zero]

/-- **Method II** (bias adaption): with `τ_{p+1} = 1` and
`β_{p+1}(f) = -∑_{k ≤ p} β_k(f) ⟨φ τ_k⟩ / ⟨φ⟩` (`⟨φ⟩ ≠ 0`), the DeepONet preserves the
invariant. -/
theorem deepONet_preserves_biasAdapted (w φ : V → ℝ) (hφ : avg w φ ≠ 0)
    (β : (V → ℝ) → Fin (p + 1) → ℝ) (τ : Fin (p + 1) → V → ℝ) (hlast : τ (Fin.last p) = 1)
    (hβ : ∀ f, β f (Fin.last p) =
      -(∑ k : Fin p, β f k.castSucc * avg w (fun v => φ v * τ k.castSucc v)) / avg w φ) :
    HasInvariant w φ (deepONet β τ) := by
  intro f
  rw [avg_deepONet, Fin.sum_univ_castSucc, hβ, hlast]
  simp only [Pi.one_apply, mul_one]
  field_simp
  ring

/-- **Mass rescaling** (Eq. (15)): `Q_θ(f) = ⟨f⟩ Q_θ(f / ⟨f⟩)` keeps every collision invariant of
the network trained on unit-mass densities. -/
theorem massRescale_preserves {w φ : V → ℝ} {Q : (V → ℝ) → V → ℝ} (hQ : HasInvariant w φ Q) :
    HasInvariant w φ (fun f v => avg w f * Q ((avg w f)⁻¹ • f) v) := by
  intro f
  have h := hQ ((avg w f)⁻¹ • f)
  calc avg w (fun v => φ v * (avg w f * Q ((avg w f)⁻¹ • f) v))
      = avg w f * avg w (fun v => φ v * Q ((avg w f)⁻¹ • f) v) := by
        rw [← avg_const_mul]; congr 1; funext v; ring
    _ = 0 := by rw [h, mul_zero]

/-- **Algorithm 3**: with `m₁ ≡ c > 0` (here the zeroth entry of the basis) and
`α₁ = -(log m₁ + log ⟨exp(α_# · m_#)⟩)/m₁`, the sampled density `exp(α · m)` has unit mass
(`P2106_09445a.zerothMoment_eq_one_iff`). -/
theorem samplingMultiplier_mass_eq_one [Nonempty V] {n : ℕ} {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {m : V → Fin (n + 1) → ℝ} {c : ℝ} (hc : 0 < c) (hm0 : ∀ v, m v 0 = c) (αs : Fin n → ℝ) :
    moments w m (ansatz m (Fin.cons (zerothMultiplier w c (reducedBasis m) αs) αs)) 0 = 1 :=
  (zerothMoment_eq_one_iff hw hc hm0 _ αs).2 rfl

/-! ### Conservation of mass in the hybrid system (connection to the core) -/

/-- The collision field `f ↦ σ_s Q(f)` of the hybrid system (17) on the Euclidean space of
sensor values. -/
def collisionField (σs : ℝ) (Q : (V → ℝ) → V → ℝ) (f : EuclideanSpace ℝ V) :
    EuclideanSpace ℝ V :=
  WithLp.toLp 2 (σs • Q (WithLp.ofLp f))

/-- The conserved direction `c = w φ`, so that `⟪c, f⟫ = ⟨φ f⟩`. -/
def massDir (w φ : V → ℝ) : EuclideanSpace ℝ V := WithLp.toLp 2 fun v => w v * φ v

lemma inner_massDir (w φ : V → ℝ) (f : EuclideanSpace ℝ V) :
    ⟪massDir w φ, f⟫ = avg w fun v => φ v * WithLp.ofLp f v := by
  simp only [massDir, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, avg]
  exact sum_congr rfl fun v _ => by ring

/-- The collision field of an operator with the invariant `φ` is orthogonal to `w φ`. -/
theorem inner_massDir_collisionField {w φ : V → ℝ} {Q : (V → ℝ) → V → ℝ}
    (hQ : HasInvariant w φ Q) (σs : ℝ) (f : EuclideanSpace ℝ V) :
    ⟪massDir w φ, collisionField σs Q f⟫ = 0 := by
  rw [inner_massDir]
  have h := hQ (WithLp.ofLp f)
  calc avg w (fun v => φ v * WithLp.ofLp (collisionField σs Q f) v)
      = σs * avg w (fun v => φ v * Q (WithLp.ofLp f) v) := by
        rw [← avg_const_mul]; congr 1; funext v
        simp only [collisionField, WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]
        ring
    _ = 0 := by rw [h, mul_zero]

/-- **Mass conservation** of the collision part of the hybrid system (17): an explicit Euler step
(core `eulerStep`) with a collision DeepONet that has the invariant conserves `⟨φ f⟩`. -/
theorem mass_eulerStep_eq {w φ : V → ℝ} {Q : (V → ℝ) → V → ℝ} (hQ : HasInvariant w φ Q)
    (σs h : ℝ) (f : EuclideanSpace ℝ V) :
    ⟪massDir w φ, eulerStep (collisionField σs Q) h f⟫ = ⟪massDir w φ, f⟫ := by
  rw [eulerStep, inner_add_right, inner_smul_right, inner_massDir_collisionField hQ, mul_zero,
    add_zero]

/-- Iterated explicit Euler steps conserve the mass (core `inner_eq_of_forall_step`). -/
theorem mass_eulerStep_iter_eq {w φ : V → ℝ} {Q : (V → ℝ) → V → ℝ} (hQ : HasInvariant w φ Q)
    (σs h : ℝ) (f₀ : EuclideanSpace ℝ V) (k : ℕ) :
    ⟪massDir w φ, (eulerStep (collisionField σs Q) h)^[k] f₀⟫ = ⟪massDir w φ, f₀⟫ := by
  refine inner_eq_of_forall_step (Y := fun k => (eulerStep (collisionField σs Q) h)^[k] f₀)
    (fun k => ?_) k
  simp only [Function.iterate_succ_apply']
  exact mass_eulerStep_eq hQ σs h _

/-- **Mass conservation under low-rank Galerkin steps**: if an orthogonal projector `P` (e.g. a
DLRA velocity basis containing `φ`) fixes the mass direction, the explicit Euler Galerkin step
`f ↦ P (P f + h σ_s Q_θ(P f))` conserves the mass (core `galerkinEulerStep_inner_eq`). -/
theorem mass_galerkinEulerStep_eq {w φ : V → ℝ} {Q : (V → ℝ) → V → ℝ} (hQ : HasInvariant w φ Q)
    {P : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V} (hP : IsOrthProj P)
    (hc : P (massDir w φ) = massDir w φ) (σs h : ℝ) (f : EuclideanSpace ℝ V) :
    ⟪massDir w φ, galerkinEulerStep P (collisionField σs Q) h f⟫ = ⟪massDir w φ, f⟫ :=
  galerkinEulerStep_inner_eq hP hc (inner_massDir_collisionField hQ σs _)

/-- Non-vacuity: the zero trunk extended by `τ_{p+1} = φ` with `β_{p+1} = 0` satisfies the
hypotheses of Method I. -/
example (w φ : V → ℝ) (β : (V → ℝ) → Fin (p + 1) → ℝ) :
    HasInvariant w φ (deepONet (fun f k => if k = Fin.last p then 0 else β f k)
      (fun k => if k = Fin.last p then φ else 0)) :=
  deepONet_preserves_of_orthogonal w φ _ _ (by simp) (by simp)
    (fun k => by simp [avg, (Fin.castSucc_lt_last k).ne])

end LeanDLRA.Literature.P2402_16613

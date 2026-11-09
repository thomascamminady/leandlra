import LeanDLRA.Integrators.BUG
import LeanDLRA.Matrix.Projectors
import LeanDLRA.Foundations.Galerkin

/-!
# Results of arXiv 1710.03946: Dynamics, numerical analysis, and some geometry

Gauckler–Hairer–Lubich, *Dynamics, numerical analysis, and some geometry* (survey).
Sec. 6.1 (TDVP for the Schroedinger equation), abstract form: on a complex inner product space `E`
(not necessarily finite dimensional, no manifold structure is modelled) let `H` be a bounded
self-adjoint complex-linear operator and let `P u` be, for every state `u`, a real-orthogonal
projector onto a complex-linear subspace (the tangent space `T_u M`, encoded by commutation with
multiplication by `I`).  For trajectories of the state-dependent Galerkin equation
`u' = P_u (-I H u)` we prove conservation of the energy `⟨u, H u⟩` and of the norm `‖u‖` whenever
`u ∈ T_u M`, as well as the symplectic properties of `P_u` with respect to `ω(x, y) = Im ⟨x, y⟩`.
This extends the fixed projector energy conservation `ODESolution.galerkin_energy_eq_of_skew`.

Differences from the paper: the paper's Hamiltonian on `L²` is in general unbounded, here `H` is a
continuous linear map; the paper's symplectic form is `2 Im ⟨ξ, η⟩`, here the factor `2` is
dropped (it does not affect the stated properties); the paper's condition for norm conservation
("`M` contains rays") is replaced by its consequence `u ∈ T_u M`.  The Hamiltonian
reformulation `ω(u̇, v) = dH(u)[v]`, the symplectic manifold structure of `M` and the
symplecticity of the flow are not formalized.
-/

open Set Filter Topology Finset Complex
open scoped RealInnerProductSpace ComplexConjugate

namespace LeanDLRA.Literature.P1710_03946

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

attribute [local instance] InnerProductSpace.complexToReal

/-- The standard symplectic form `ω(x, y) = Im ⟨x, y⟩` of a complex inner product space (the
paper, Sec. 6.1, uses `2 Im ⟨ξ, η⟩`; the factor does not matter for the results below). -/
noncomputable def omega (x y : E) : ℝ := (inner ℂ x y).im

lemma omega_eq_neg_real_inner (x y : E) : omega x y = -⟪x, (I : ℂ) • y⟫ := by
  rw [omega, real_inner_eq_re_inner (𝕜 := ℂ), inner_smul_right]
  simp

/-- **Sec. 6.1, symplecticity of `P_u`** (arXiv 1710.03946), abstract form: a real orthogonal
projector `P` commuting with multiplication by `I` (i.e. onto a complex-linear subspace) is
self-adjoint for `ω`, `ω(P x, y) = ω(x, P y)`, and `ω(P x, (1 - P) y) = 0`: the range and the
kernel of `P` are `ω`-orthogonal, so `P` is the symplectic projection as well. -/
theorem omega_proj_symm {P : E →L[ℝ] E} (hP : IsOrthProj P)
    (hPI : ∀ x, P ((I : ℂ) • x) = (I : ℂ) • P x) (x y : E) :
    omega (P x) y = omega x (P y) ∧ omega (P x) (y - P y) = 0 := by
  have h1 : ∀ x y, omega (P x) y = omega x (P y) := by
    intro x y
    rw [omega_eq_neg_real_inner, omega_eq_neg_real_inner, hP.symm, hPI]
  refine ⟨h1 x y, ?_⟩
  rw [h1, map_sub, hP.idem, sub_self]
  simp [omega]

variable {P : E → E →L[ℝ] E} {H : E →L[ℂ] E} {u : ℝ → E} {a b : ℝ}

lemma real_inner_I_smul_self (z : E) : ⟪z, (I : ℂ) • z⟫ = 0 := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [← ofReal_pow]

lemma inner_self_adjoint_im (hH : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) (x : E) :
    (inner ℂ x (H x)).im = 0 := by
  have h : inner ℂ x (H x) = conj (inner ℂ x (H x)) := by
    rw [inner_conj_symm, hH]
  exact conj_eq_iff_im.1 h.symm

/-- **Sec. 6.1, energy conservation of TDVP for the Schroedinger equation** (arXiv 1710.03946),
abstract form with a state-dependent projector.  If `H` is self-adjoint, every `P_u` is a real
orthogonal projector onto a complex-linear subspace (commuting with `I`) and `u` solves
`u' = P_u (-I H u)` (right derivatives on `[a, b)`, continuity on `[a, b]`), then
`⟨u(t), H u(t)⟩` is constant.  The tangent-space property of the paper is the only structure used;
manifold smoothness of `u ↦ P_u` is not needed, and neither is any condition on `u a`.  `H` is
bounded here (a continuous linear map), unlike the general Hamiltonian of the paper. -/
theorem energy_conservation (hP : ∀ x, IsOrthProj (P x))
    (hPI : ∀ x z, P x ((I : ℂ) • z) = (I : ℂ) • P x z)
    (hH : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (hu : LeanDLRA.ODESolution (fun _ x => P x (-((I : ℂ) • H x))) u a b) :
    ∀ t ∈ Icc a b, inner ℂ (u t) (H (u t)) = inner ℂ (u a) (H (u a)) := by
  set A : E →L[ℝ] E := (H : E →L[ℂ] E).restrictScalars ℝ with hA
  have hAs : ∀ x y : E, ⟪A x, y⟫ = ⟪x, A y⟫ := by
    intro x y
    simp only [hA, real_inner_eq_re_inner (𝕜 := ℂ), ContinuousLinearMap.coe_restrictScalars',
      hH]
  have hℰ := fun x => LeanDLRA.hasFDerivAt_half_inner_apply_self hAs x
  have hc : ∀ t ∈ Icc a b, (fun x : E => ⟪x, A x⟫ / 2) (u t) =
      (fun x : E => ⟪x, A x⟫ / 2) (u a) := by
    refine constant_of_has_deriv_right_zero
      ((LeanDLRA.continuous_of_hasFDerivAt_innerSL hℰ).comp_continuousOn hu.cont)
      fun t ht => (LeanDLRA.hasDerivWithinAt_energy_comp hℰ (hu.deriv t ht)).congr_deriv ?_
    change ⟪H (u t), P (u t) (-((I : ℂ) • H (u t)))⟫ = 0
    have hPt := hP (u t)
    set w := H (u t)
    have key : ⟪w, (I : ℂ) • P (u t) w⟫ = 0 := by
      calc ⟪w, (I : ℂ) • P (u t) w⟫ = ⟪w, P (u t) ((I : ℂ) • w)⟫ := by rw [hPI]
        _ = ⟪P (u t) w, (I : ℂ) • w⟫ := (hPt.symm _ _).symm
        _ = ⟪P (u t) (P (u t) w), (I : ℂ) • w⟫ := by rw [hPt.idem]
        _ = ⟪P (u t) w, P (u t) ((I : ℂ) • w)⟫ := hPt.symm _ _
        _ = 0 := by rw [hPI]; exact real_inner_I_smul_self _
    rw [map_neg, hPI, inner_neg_right, key, neg_zero]
  intro t ht
  have h1 := hc t ht
  have hre : (inner ℂ (u t) (H (u t))).re = (inner ℂ (u a) (H (u a))).re := by
    have e : ∀ x : E, ⟪x, A x⟫ = (inner ℂ x (H x)).re := fun x =>
      real_inner_eq_re_inner (𝕜 := ℂ) x (H x)
    simp only [e] at h1
    linarith
  apply Complex.ext hre
  rw [inner_self_adjoint_im hH, inner_self_adjoint_im hH]

/-- **Sec. 6.1, norm conservation of TDVP for the Schroedinger equation** (arXiv 1710.03946),
abstract form with a state-dependent projector: under the hypotheses of `energy_conservation`, if
moreover `u(t) ∈ T_{u(t)} M`, i.e. `P_{u(t)} u(t) = u(t)` along the solution, then `‖u(t)‖` is
constant.  The membership is required on `[a, b)` only (where derivatives are used).  The paper
assumes instead that `M` contains rays (`αu ∈ M` for `α > 0`), which implies `u ∈ T_u M`; that
implication is not formalized (there is no manifold here). -/
theorem norm_conservation (hP : ∀ x, IsOrthProj (P x))
    (hH : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (hu : LeanDLRA.ODESolution (fun _ x => P x (-((I : ℂ) • H x))) u a b)
    (hmem : ∀ t ∈ Ico a b, P (u t) (u t) = u t) :
    ∀ t ∈ Icc a b, ‖u t‖ = ‖u a‖ := by
  have hc : ∀ t ∈ Icc a b, (fun t => ‖u t‖ ^ 2) t = (fun t => ‖u t‖ ^ 2) a := by
    refine constant_of_has_deriv_right_zero
      ((continuous_pow 2).comp_continuousOn (continuous_norm.comp_continuousOn hu.cont))
      fun t ht => (hu.deriv t ht).norm_sq.congr_deriv ?_
    change 2 * ⟪u t, P (u t) (-((I : ℂ) • H (u t)))⟫ = 0
    rw [← (hP (u t)).symm, hmem t ht]
    have him := inner_self_adjoint_im hH (u t)
    rw [real_inner_eq_re_inner (𝕜 := ℂ), inner_neg_right, inner_smul_right]
    simp [Complex.mul_re, him]
  intro t ht
  have h := hc t ht
  simp only at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- Non-vacuity: the hypotheses of `energy_conservation` and `norm_conservation` are satisfied, for
instance, by `E = ℂ`, `H = id`, `P ≡ id` and the solution `u(t) = exp(-i t)`. -/
example : ∃ u : ℝ → ℂ, LeanDLRA.ODESolution
    (fun _ x => (ContinuousLinearMap.id ℝ ℂ) (-((I : ℂ) • (ContinuousLinearMap.id ℂ ℂ) x))) u 0 1 ∧
    u 0 = 1 := by
  refine ⟨fun t => Complex.exp (-(t * I)), ⟨?_, ?_⟩, by simp⟩
  · exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(t * I))).continuousOn
  · intro t _
    have h : HasDerivAt (fun t : ℝ => Complex.exp (-(t * I)))
        (Complex.exp (-(t * I)) * (-I)) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).neg.cexp
      simpa using this
    simpa [mul_comm] using h.hasDerivWithinAt

example : LeanDLRA.IsOrthProj (ContinuousLinearMap.id ℝ ℂ) ∧
    ∀ z : ℂ,
      (ContinuousLinearMap.id ℝ ℂ) ((I : ℂ) • z) = (I : ℂ) • (ContinuousLinearMap.id ℝ ℂ) z :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

end LeanDLRA.Literature.P1710_03946

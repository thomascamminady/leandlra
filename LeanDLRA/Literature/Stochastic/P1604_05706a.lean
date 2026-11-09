import LeanDLRA.Foundations.ODE
import LeanDLRA.Foundations.Projector

/-!
# Results of arXiv 1604.05706 (Billaud-Friess, Nouy): Galerkin reduced model on a moving subspace

This module formalizes the algebraic core of the time-dependent Galerkin reduction of the paper
(Section 2.1), for an arbitrary real Hilbert space `E` (the paper takes `E = ℝ^d`) and the reduced
space `ℝ^r`. The parameter `ξ` of the paper is fixed and suppressed, and the flux is written
`f t u` for the paper's `f(u, t, ξ)`.

* `IsIsometricBasis V` says that `V : ℝ^r → E` is an orthonormal basis of its range, `Vᵀ V = I_r`,
  with `Vᵀ` the Hilbert adjoint. `basisProj V = V Vᵀ` is the orthogonal projector `Π_{X_r}`
  onto that range; it is an orthogonal projector in the sense of the core `IsOrthProj`
  (`isOrthProj_basisProj`). `reducedFlux f V dV t α = Vᵀ f(Vα, t) - Vᵀ V' α` is the reduced flux of
  Eq. (9), where `dV = V'`.
* `galerkin_iff_reduced`: for `u = V α` with `V` and `α` differentiable at `t`, the Galerkin
  condition `Π u' = Π f(u)` of Eq. (6) holds iff `α'(t) = f_r(α(t), t)`, which is Eq. (8)
  (Eqs. (7)-(9)). `galerkin_iff_reduced_ode` is the same statement on all of `ℝ`.
* `init_iff_adjoint`: the initial condition `u_r(0) = Π(0) u⁰` of Eq. (6) is equivalent to
  `α(0) = V(0)ᵀ u⁰`, as stated after Eq. (9).
* `reducedFlux_isLipschitzField` is the Lipschitz part of Remark 1: if `f(·, t)` is `L`-Lipschitz
  uniformly in `t` and `‖V'(t)‖ ≤ M`, then `f_r` is `(L + M)`-Lipschitz in `α`, uniformly in `t`.
  The remark gives no constant; `L + M` is the one of the proof.

Not formalized: the continuity part of Remark 1 and the existence and uniqueness of a global,
continuously differentiable solution of the reduced ODE (a global Picard-Lindelöf argument for a
field that is continuous and Lipschitz uniformly in `t`, not derived here), the comparison Lemma 1
(stated for integrable coefficients), the interpolation property of Section 3.1, and Proposition 1
(the a posteriori bound with the logarithmic Lipschitz constant).
-/

open Set Filter Topology Finset
open scoped RealInnerProductSpace

open _root_.ContinuousLinearMap

namespace LeanDLRA.Literature.P1604_05706

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `V : ℝ^r → E` is an orthonormal basis of its range, i.e. `Vᵀ V = I_r`: the columns of `V`
are orthonormal. Here `Vᵀ` is the Hilbert adjoint `adjoint V`. -/
def IsIsometricBasis {r : ℕ} (V : EuclideanSpace ℝ (Fin r) →L[ℝ] E) : Prop :=
  ∀ a, adjoint V (V a) = a

/-- The orthogonal projector `Π_{X_r} = V Vᵀ` onto the range of `V`. -/
noncomputable def basisProj {r : ℕ} (V : EuclideanSpace ℝ (Fin r) →L[ℝ] E) : E →L[ℝ] E :=
  V ∘L adjoint V

/-- The reduced flux of Eq. (9): `f_r(α, t) = Vᵀ f(V α, t) - Vᵀ V' α`, where `dV = V'`. -/
noncomputable def reducedFlux {r : ℕ} (f : ℝ → E → E)
    (V dV : ℝ → EuclideanSpace ℝ (Fin r) →L[ℝ] E)
    (t : ℝ) (a : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin r) :=
  adjoint (V t) (f t (V t a)) - adjoint (V t) (dV t a)

section Basic

variable {r : ℕ} {V : EuclideanSpace ℝ (Fin r) →L[ℝ] E}

lemma adjoint_V_apply (hV : IsIsometricBasis V) (a : EuclideanSpace ℝ (Fin r)) :
    adjoint V (V a) = a :=
  hV a

lemma basisProj_apply (x : E) : basisProj V x = V (adjoint V x) := rfl

lemma isometric_norm_apply (hV : IsIsometricBasis V) (a : EuclideanSpace ℝ (Fin r)) :
    ‖V a‖ = ‖a‖ := by
  have h1 : ⟪a, adjoint V (V a)⟫ = ⟪V a, V a⟫ := adjoint_inner_right V a (V a)
  rw [adjoint_V_apply hV a, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  nlinarith [norm_nonneg (V a), norm_nonneg a]

lemma adjoint_norm_apply_le (hV : IsIsometricBasis V) (x : E) :
    ‖adjoint V x‖ ≤ ‖x‖ := by
  have h1 : ⟪adjoint V x, adjoint V x⟫ = ⟪V (adjoint V x), x⟫ :=
    adjoint_inner_right V (adjoint V x) x
  have h2 : ⟪V (adjoint V x), x⟫ ≤ ‖V (adjoint V x)‖ * ‖x‖ := real_inner_le_norm _ _
  rw [isometric_norm_apply hV] at h2
  have h3 : ⟪adjoint V x, adjoint V x⟫ = ‖adjoint V x‖ * ‖adjoint V x‖ :=
    real_inner_self_eq_norm_mul_norm _
  nlinarith [norm_nonneg x, norm_nonneg (adjoint V x)]

/-- `Π = V Vᵀ` is an orthogonal projector in the sense of the core `IsOrthProj`. -/
lemma isOrthProj_basisProj (hV : IsIsometricBasis V) : IsOrthProj (basisProj V) where
  idem x := by
    simp only [basisProj_apply, adjoint_V_apply hV]
  symm x y := by
    simp only [basisProj_apply]
    rw [← adjoint_inner_right, adjoint_inner_left]

end Basic

section Galerkin

variable {r : ℕ} {V : EuclideanSpace ℝ (Fin r) →L[ℝ] E}

/-- Pointwise core of Eqs. (6)-(9): if `u' = w + V a'`, then `Π u' = Π g` iff
`a' = Vᵀ g - Vᵀ w`. -/
lemma basisProj_eq_iff (hV : IsIsometricBasis V) (a' : EuclideanSpace ℝ (Fin r)) (w g : E) :
    basisProj V (w + V a') = basisProj V g ↔ a' = adjoint V g - adjoint V w := by
  constructor
  · intro h
    have h2 := congrArg (adjoint V) h
    simp only [basisProj_apply, adjoint_V_apply hV, map_add] at h2
    rw [← h2]
    abel
  · intro h
    have key : adjoint V (w + V a') = adjoint V g := by
      rw [h]
      simp only [map_add, map_sub, adjoint_V_apply hV]
      abel
    rw [basisProj_apply, basisProj_apply, key]

/-- **Eqs. (6)-(9), at one time** (arXiv 1604.05706, Section 2.1). Let `a` be differentiable at
  `t` with derivative `a'`, and
`V` differentiable at `t` with derivative `V'(t) = dV t`. Put `u = V α`. The Galerkin condition
`Π_{X_r(t)} u' = Π f(u)` of Eq. (6) holds at `t` iff `α'(t) = f_r(α(t), t)` with the reduced flux
of Eq. (9). -/
theorem galerkin_iff_reduced {f : ℝ → E → E} {V dV : ℝ → EuclideanSpace ℝ (Fin r) →L[ℝ] E}
    {a : ℝ → EuclideanSpace ℝ (Fin r)} {a' : EuclideanSpace ℝ (Fin r)} {u' : E} {t : ℝ}
    (hV : IsIsometricBasis (V t)) (hVd : HasDerivAt V (dV t) t)
    (ha : HasDerivAt a a' t) (hu : HasDerivAt (fun s => V s (a s)) u' t) :
    basisProj (V t) u' = basisProj (V t) (f t (V t (a t))) ↔
      a' = reducedFlux f V dV t (a t) := by
  have hu' : u' = dV t (a t) + V t a' := hu.unique (hVd.clm_apply ha)
  rw [hu']
  exact basisProj_eq_iff hV a' (dV t (a t)) (f t (V t (a t)))

/-- **Eqs. (6)-(9), on all of `ℝ`** (arXiv 1604.05706, Section 2.1). If `V(t)` is an orthonormal
  basis for every `t`, and `u = V α`
satisfies the Galerkin condition (6) for every `t`, then `α` solves the reduced system (8) with
the reduced flux (9) for every `t`. -/
theorem galerkin_iff_reduced_ode {f : ℝ → E → E} {V dV : ℝ → EuclideanSpace ℝ (Fin r) →L[ℝ] E}
    {a a' : ℝ → EuclideanSpace ℝ (Fin r)} {u' : ℝ → E}
    (hV : ∀ t, IsIsometricBasis (V t)) (hVd : ∀ t, HasDerivAt V (dV t) t)
    (ha : ∀ t, HasDerivAt a (a' t) t) (hu : ∀ t, HasDerivAt (fun s => V s (a s)) (u' t) t) :
    (∀ t, basisProj (V t) (u' t) = basisProj (V t) (f t (V t (a t)))) ↔
      ∀ t, a' t = reducedFlux f V dV t (a t) :=
  forall_congr' fun t => galerkin_iff_reduced (hV t) (hVd t) (ha t) (hu t)

/-- The initial condition of Eq. (6), `u_r(0) = Π(0) u⁰` with `u_r(0) = V(0) α(0)`, holds iff
`α(0) = V(0)ᵀ u⁰`. -/
lemma init_iff_adjoint (hV : IsIsometricBasis V) (a0 : EuclideanSpace ℝ (Fin r)) (u0 : E) :
    V a0 = basisProj V u0 ↔ a0 = adjoint V u0 := by
  constructor
  · intro h
    have h2 := congrArg (adjoint V) h
    simpa only [adjoint_V_apply hV, basisProj_apply] using h2
  · intro h
    rw [basisProj_apply, h]

end Galerkin

section Lipschitz

variable {r : ℕ}

/-- **Remark 1 (Lipschitz part), arXiv 1604.05706.** If `f(·, t)` is `L`-Lipschitz uniformly in
`t`, `V(t)` is an orthonormal basis for every `t`, and `‖V'(t)‖ ≤ M` for all `t`, then the reduced
flux (9) is `(L + M)`-Lipschitz in `α`, uniformly in `t`. The remark states no constant; `L + M`
is the one its argument gives. The statement needs neither that `dV` is the derivative of `V` nor
the continuity hypotheses of the remark, so it is slightly more general. -/
theorem reducedFlux_isLipschitzField {f : ℝ → E → E}
    {V dV : ℝ → EuclideanSpace ℝ (Fin r) →L[ℝ] E}
    {L M : ℝ} (hV : ∀ t, IsIsometricBasis (V t)) (hf : IsLipschitzField f L)
    (hdV : ∀ t, ‖dV t‖ ≤ M) : IsLipschitzField (reducedFlux f V dV) (L + M) := by
  intro t x y
  have hVxy : ‖V t x - V t y‖ = ‖x - y‖ := by
    rw [← map_sub, isometric_norm_apply (hV t)]
  have h1 : ‖adjoint (V t) (f t (V t x) - f t (V t y))‖ ≤ L * ‖x - y‖ := by
    refine (adjoint_norm_apply_le (hV t) _).trans ?_
    have := hf t (V t x) (V t y)
    rw [hVxy] at this
    exact this
  have h2 : ‖adjoint (V t) (dV t (x - y))‖ ≤ M * ‖x - y‖ := by
    refine (adjoint_norm_apply_le (hV t) _).trans ?_
    calc ‖dV t (x - y)‖ ≤ ‖dV t‖ * ‖x - y‖ := (dV t).le_opNorm _
      _ ≤ M * ‖x - y‖ := mul_le_mul_of_nonneg_right (hdV t) (norm_nonneg _)
  have heq : reducedFlux f V dV t x - reducedFlux f V dV t y =
      adjoint (V t) (f t (V t x) - f t (V t y)) - adjoint (V t) (dV t (x - y)) := by
    unfold reducedFlux
    simp only [map_sub]
    abel
  rw [heq]
  calc ‖adjoint (V t) (f t (V t x) - f t (V t y)) - adjoint (V t) (dV t (x - y))‖
      ≤ ‖adjoint (V t) (f t (V t x) - f t (V t y))‖ + ‖adjoint (V t) (dV t (x - y))‖ :=
        norm_sub_le _ _
    _ ≤ L * ‖x - y‖ + M * ‖x - y‖ := add_le_add h1 h2
    _ = (L + M) * ‖x - y‖ := by ring

/-- Nonvacuity: the identity map of `ℝ^r` is an orthonormal basis of itself. -/
example : IsIsometricBasis (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin r))) := by
  unfold IsIsometricBasis
  intro a
  simp [_root_.ContinuousLinearMap.adjoint_id]

end Lipschitz

end LeanDLRA.Literature.P1604_05706

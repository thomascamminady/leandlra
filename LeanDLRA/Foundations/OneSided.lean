import LeanDLRA.Foundations.ODE
import LeanDLRA.Analysis.Defs

/-!
# One-sided Lipschitz vector fields: stability for stiff and dissipative problems

For stiff problems (parabolic PDEs after spatial discretisation, Sylvester/Lyapunov-type matrix
ODEs with a diffusive linear part) the Lipschitz constant `L` of the vector field blows up under
mesh refinement, and Grönwall bounds of the form `exp (L t)` become useless.  Robust error
analysis of dynamical low-rank approximation for such problems therefore replaces `L` by the
**one-sided Lipschitz constant** `ℓ`, defined by

    ⟪F t x - F t y, x - y⟫ ≤ ℓ ‖x - y‖²     for all t, x, y,

(Carrel–Vandereycken, arXiv 2312.00172, Definition 1).  It can be much smaller than `L`, and it
is negative for diffusive (dissipative) problems.  For a linear operator it is the logarithmic
norm `sup ⟪A w, w⟫ / ‖w‖²`.

## Main results

* `IsOneSidedLipschitzField F ℓ`, and its localised version `IsOneSidedLipschitzOn F K ℓ`
  (one-sided condition only on a set `K`, the "energy-localised region" of Hu–Yu,
  arXiv 2610.41606, §3, eq. (3.3)).
* Calculus: Lipschitz with `L` ⇒ one-sided with `ℓ = L`; sums (`ℓ_{F+G} ≤ ℓ_F + ℓ_G`, hence
  `ℓ_{L+G} ≤ ℓ_L + L_G`, Carrel–Vandereycken Remark 1); state-independent forcing terms do not
  change `ℓ`; linear operators (`ℓ` = logarithmic-norm bound `⟪A x, x⟫ ≤ μ ‖x‖²`); dissipative
  linear operators (`⟪A x, x⟫ ≤ 0`) give `ℓ = 0`; negatives of strongly monotone operators.
* `norm_sub_le_gronwallBound_of_inner_le`: the **stability theorem** for two approximate
  solutions `y' = u`, `z' = w` with defects `‖u - F(y)‖ ≤ ηy`, `‖w - F(z)‖ ≤ ηz`, assuming the
  one-sided inequality only *along the two trajectories*:

      ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a)
                  = exp (ℓ (t-a)) δ + (t - a) φ₁(ℓ (t - a)) (ηy + ηz),

  where `φ₁(z) = (exp z - 1)/z`.  This holds for **every real `ℓ`** (no sign condition), which is
  exactly the form of Carrel–Vandereycken, arXiv 2312.00172, Theorem 7, and of Hu–Yu,
  arXiv 2610.41606, §3 (`e(t) ≤ exp (μ t) e(0)`).
* Explicit bounds for `gronwallBound` with arbitrary real `ℓ`: `exp(ℓx) δ + η x max 1 (exp(ℓx))`
  for all `ℓ`, `exp(ℓx) (δ + η x)` for `ℓ ≥ 0`, `exp(ℓx) δ + η x` for `ℓ ≤ 0`, and the
  time-uniform bound `exp(ℓx) δ + η / (-ℓ)` for `ℓ < 0`.
* Corollaries for exact solutions (`ODESolution`): `‖y t - z t‖ ≤ exp (ℓ (t-a)) ‖y a - z a‖`,
  forward uniqueness for one-sided Lipschitz fields, non-expansiveness of dissipative flows, and
  the error bound for a perturbed problem `Y' = G(t, Y)` with `‖G(t,Y) - F(t,Y)‖ ≤ ε` along `Y`
  (the DLRA situation `G(t, Y) = P(Y) F(t, Y)`; Carrel–Vandereycken Theorem 7).
* **Projected (Galerkin) fields.**  If `F` is one-sided Lipschitz with `ℓ` and `P` is an
  orthogonal projector, then `x ↦ P (F t x)` is one-sided Lipschitz with the same `ℓ` on the
  range of `P`.  Hence Galerkin trajectories `y' = P F(t, y)` started in the range of `P` satisfy
  the same stability bound, and a Galerkin trajectory approximates the exact solution up to
  `exp(ℓ(t-a)) δ + (t-a) φ₁(ℓ(t-a)) ε` where `ε` bounds the neglected component
  `‖F(Y) - P F(Y)‖` — the basis of robust error bounds for stiff DLRA.
* **Implicit (Galerkin) Euler steps.**  For `x₁ = P (x₀ + h F(t, x₁))` the one-sided condition
  gives `(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖` (with residuals: Hu–Yu, arXiv 2610.41606, eq. (5.7)
  and uniqueness argument in Theorem 5.1), uniqueness of the implicit stage when `h ℓ < 1`, and
  norm-nonincrease of the implicit Galerkin step for dissipative fields
  (Appelö–Cheng, arXiv 2402.05347, Theorem 3.1, Galerkin part).

## Implementation notes

The continuous stability theorem is proved by applying Mathlib's
`le_gronwallBound_of_liminf_deriv_right_le` to `t ↦ ‖y t - z t‖`.  Its right Dini derivative is
bounded by `ℓ ‖y - z‖ + ηy + ηz`: where `y t ≠ z t` the norm is differentiable with derivative
`⟪e, e'⟫ / ‖e‖`, and where `y t = z t` the fields agree, so `‖e'‖ ≤ ηy + ηz`.  Mathlib's
`gronwallBound` is defined for every real rate, so no sign condition on `ℓ` is needed.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LeanDLRA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Definitions

`IsOneSidedLipschitzField` and `IsOneSidedLipschitzOn` are defined in
`LeanDLRA/Analysis/Defs.lean`. -/

/-! ### Calculus of one-sided Lipschitz constants -/

namespace IsOneSidedLipschitzField

variable {F G : ℝ → E → E} {ℓ ℓ' : ℝ}

/-- A one-sided Lipschitz constant can be enlarged. -/
lemma mono (hF : IsOneSidedLipschitzField F ℓ) (h : ℓ ≤ ℓ') : IsOneSidedLipschitzField F ℓ' :=
  fun t x y => (hF t x y).trans (mul_le_mul_of_nonneg_right h (by positivity))

/-- A global one-sided Lipschitz condition implies the localised one on every set. -/
lemma isOneSidedLipschitzOn (hF : IsOneSidedLipschitzField F ℓ) (K : Set E) :
    IsOneSidedLipschitzOn F K ℓ :=
  fun t x _ y _ => hF t x y

/-- One-sided Lipschitz constants are subadditive: `ℓ_{F+G} ≤ ℓ_F + ℓ_G`. -/
lemma add (hF : IsOneSidedLipschitzField F ℓ) (hG : IsOneSidedLipschitzField G ℓ') :
    IsOneSidedLipschitzField (fun t x => F t x + G t x) (ℓ + ℓ') := fun t x y => by
  have h : F t x + G t x - (F t y + G t y) = (F t x - F t y) + (G t x - G t y) := by abel
  rw [h, inner_add_left, add_mul]
  exact add_le_add (hF t x y) (hG t x y)

/-- Adding a state-independent forcing term `g t` does not change the one-sided Lipschitz
constant. -/
lemma add_forcing (hF : IsOneSidedLipschitzField F ℓ) (g : ℝ → E) :
    IsOneSidedLipschitzField (fun t x => F t x + g t) ℓ := fun t x y => by
  simpa only [add_sub_add_right_eq_sub] using hF t x y

/-- Scaling by a nonnegative factor scales the one-sided Lipschitz constant. -/
lemma smul (hF : IsOneSidedLipschitzField F ℓ) {c : ℝ} (hc : 0 ≤ c) :
    IsOneSidedLipschitzField (fun t x => c • F t x) (c * ℓ) := fun t x y => by
  rw [← smul_sub, real_inner_smul_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF t x y) hc

end IsOneSidedLipschitzField

/-- A Lipschitz field with constant `L` is one-sided Lipschitz with constant `L` (by
Cauchy–Schwarz).  The converse fails badly for stiff problems, where `ℓ ≪ L`. -/
lemma IsLipschitzField.isOneSidedLipschitzField {F : ℝ → E → E} {L : ℝ}
    (hF : IsLipschitzField F L) : IsOneSidedLipschitzField F L := fun t x y =>
  calc ⟪F t x - F t y, x - y⟫ ≤ ‖F t x - F t y‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ L * ‖x - y‖ * ‖x - y‖ := mul_le_mul_of_nonneg_right (hF t x y) (norm_nonneg _)
    _ = L * ‖x - y‖ ^ 2 := by ring

/-- Stiff plus non-stiff splitting `F = A + G`: if `A` is one-sided Lipschitz with `ℓ` and `G` is
Lipschitz with `L`, then `A + G` is one-sided Lipschitz with `ℓ + L`
(Carrel–Vandereycken, arXiv 2312.00172, Remark 1: `ℓ_F ≤ ℓ_L + L_G`). -/
lemma IsOneSidedLipschitzField.add_lipschitz {F G : ℝ → E → E} {ℓ L : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hG : IsLipschitzField G L) :
    IsOneSidedLipschitzField (fun t x => F t x + G t x) (ℓ + L) :=
  hF.add hG.isOneSidedLipschitzField

/-- For a (time-dependent) linear field `x ↦ A t x`, the one-sided Lipschitz condition with
constant `μ` is equivalent to the logarithmic-norm bound `⟪A t x, x⟫ ≤ μ ‖x‖²`
(Carrel–Vandereycken, arXiv 2312.00172, after Definition 1). -/
lemma isOneSidedLipschitzField_linear_iff (A : ℝ → E →L[ℝ] E) (μ : ℝ) :
    IsOneSidedLipschitzField (fun t x => A t x) μ ↔ ∀ t x, ⟪A t x, x⟫ ≤ μ * ‖x‖ ^ 2 := by
  constructor
  · intro h t x
    simpa using h t x 0
  · intro h t x y
    rw [← map_sub]
    exact h t (x - y)

/-- **Dissipative linear operators** (`⟪A t x, x⟫ ≤ 0`, e.g. a discretised Laplacian), plus an
arbitrary forcing term, give a one-sided Lipschitz field with `ℓ = 0`, independently of the
(possibly huge) operator norm of `A`. -/
lemma isOneSidedLipschitzField_of_dissipative (A : ℝ → E →L[ℝ] E)
    (hA : ∀ t x, ⟪A t x, x⟫ ≤ 0) (g : ℝ → E) :
    IsOneSidedLipschitzField (fun t x => A t x + g t) 0 :=
  IsOneSidedLipschitzField.add_forcing
    ((isOneSidedLipschitzField_linear_iff A 0).2 fun t x => by simpa using hA t x) g

/-- The scalar field `x ↦ c • x` has one-sided Lipschitz constant exactly `c` (negative for
`c < 0`, while its Lipschitz constant is `|c|`). -/
lemma isOneSidedLipschitzField_smul_id (c : ℝ) :
    IsOneSidedLipschitzField (fun _ (x : E) => c • x) c := fun _ x y => by
  rw [← smul_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The negative of a strongly monotone operator (`μ ‖x - y‖² ≤ ⟪G x - G y, x - y⟫`, e.g. a
discretised elliptic operator with coercivity constant `μ`) is one-sided Lipschitz with
constant `-μ`. -/
lemma isOneSidedLipschitzField_neg_of_strongMono {G : ℝ → E → E} {μ : ℝ}
    (hG : ∀ t x y, μ * ‖x - y‖ ^ 2 ≤ ⟪G t x - G t y, x - y⟫) :
    IsOneSidedLipschitzField (fun t x => -G t x) (-μ) := fun t x y => by
  have h : -G t x - -G t y = -(G t x - G t y) := by abel
  rw [h, inner_neg_left, neg_mul]
  exact neg_le_neg (hG t x y)

/-- A stiff dissipative example: `x ↦ -100 x` has Lipschitz constant `100` but one-sided
Lipschitz constant `-100`. -/
example : IsOneSidedLipschitzField (fun _ (x : E) => (-100 : ℝ) • x) (-100) :=
  isOneSidedLipschitzField_smul_id _

/-! ### Projected (Galerkin) fields -/

section Projected

variable {F : ℝ → E → E} {ℓ : ℝ} {P : E →L[ℝ] E}

/-- **Galerkin projection keeps the one-sided Lipschitz constant.**  For `x, y` in the range of
an orthogonal projector `P`:  `⟪P (F t x) - P (F t y), x - y⟫ ≤ ℓ ‖x - y‖²`. -/
lemma IsOneSidedLipschitzField.inner_proj_sub_le (hF : IsOneSidedLipschitzField F ℓ)
    (hP : IsOrthProj P) (t : ℝ) {x y : E} (hx : P x = x) (hy : P y = y) :
    ⟪P (F t x) - P (F t y), x - y⟫ ≤ ℓ * ‖x - y‖ ^ 2 := by
  rw [← map_sub, hP.symm, map_sub, hx, hy]
  exact hF t x y

/-- The projected field `x ↦ P (F t x)` is one-sided Lipschitz with the same constant on the
range of the orthogonal projector `P`. -/
lemma IsOneSidedLipschitzField.proj (hF : IsOneSidedLipschitzField F ℓ) (hP : IsOrthProj P) :
    IsOneSidedLipschitzOn (fun t x => P (F t x)) {x | P x = x} ℓ :=
  fun t _ hx _ hy => hF.inner_proj_sub_le hP t hx hy

/-- The compressed field `x ↦ P (F t (P x))` is globally one-sided Lipschitz with constant
`max ℓ 0` (on the range of `P` it has constant `ℓ`, on the complement it vanishes). -/
lemma IsOneSidedLipschitzField.compress (hF : IsOneSidedLipschitzField F ℓ) (hP : IsOrthProj P) :
    IsOneSidedLipschitzField (fun t x => P (F t (P x))) (max ℓ 0) := fun t x y => by
  have h1 : ⟪P (F t (P x)) - P (F t (P y)), x - y⟫ = ⟪F t (P x) - F t (P y), P x - P y⟫ := by
    rw [← map_sub, hP.symm, map_sub]
  have h2 : ‖P x - P y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [← map_sub]
    exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_le _) 2
  rw [h1]
  calc ⟪F t (P x) - F t (P y), P x - P y⟫ ≤ ℓ * ‖P x - P y‖ ^ 2 := hF t _ _
    _ ≤ max ℓ 0 * ‖P x - P y‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max ℓ 0 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

end Projected

/-! ### The continuous stability theorem -/

/-- Right derivative of the norm of a curve at a point where the curve does not vanish:
`d/dt ‖e t‖ = ⟪e t, e' t⟫ / ‖e t‖`. -/
lemma hasDerivWithinAt_norm_of_ne {e : ℝ → E} {v : E} {s : Set ℝ} {x : ℝ}
    (he : HasDerivWithinAt e v s x) (h0 : e x ≠ 0) :
    HasDerivWithinAt (fun t => ‖e t‖) (⟪e x, v⟫ / ‖e x‖) s x := by
  have h2 := he.norm_sq.sqrt (by positivity : ‖e x‖ ^ 2 ≠ 0)
  have hfun : (fun t => √(‖e t‖ ^ 2)) = fun t => ‖e t‖ := by
    funext t; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun, Real.sqrt_sq (norm_nonneg _)] at h2
  convert h2 using 1
  have : ‖e x‖ ≠ 0 := norm_ne_zero_iff.2 h0
  field_simp

/-- **Stability for one-sided Lipschitz fields (approximate solutions, localised form).**
Let `y' = u` and `z' = w` on `[a, b]` with defects `‖u - F(y)‖ ≤ ηy`, `‖w - F(z)‖ ≤ ηz`, and
assume the one-sided Lipschitz inequality with constant `ℓ ∈ ℝ` only *along the two
trajectories*.  Then

    ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a)
                = exp(ℓ (t-a)) δ + (ηy + ηz) (exp(ℓ (t-a)) - 1) / ℓ.

No sign condition on `ℓ` is required.  This is the continuous stability estimate behind
Carrel–Vandereycken, arXiv 2312.00172, Theorem 7, and Hu–Yu, arXiv 2610.41606, §3 (where the
one-sided condition is only assumed in an energy-localised region); it generalises the
Lipschitz Grönwall comparison `norm_sub_le_gronwallBound` (which needs `L ≥ 0`). -/
theorem norm_sub_le_gronwallBound_of_inner_le {F : ℝ → E → E} {ℓ : ℝ}
    {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hF : ∀ t ∈ Ico a b, ⟪F t (y t) - F t (z t), y t - z t⟫ ≤ ℓ * ‖y t - z t‖ ^ 2)
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a) := by
  refine le_gronwallBound_of_liminf_deriv_right_le (f := fun t => ‖y t - z t‖)
    (f' := fun t => ℓ * ‖y t - z t‖ + (ηy + ηz)) (hyc.sub hzc).norm ?_ h0
    (fun _ _ => le_rfl)
  intro x hx r hr
  have he : HasDerivWithinAt (fun t => y t - z t) (u x - w x) (Ici x) x :=
    (hy x hx).sub (hz x hx)
  -- splitting of the velocity difference into a field part and the defects
  have hsplit : u x - w x =
      (F x (y x) - F x (z x)) + ((u x - F x (y x)) - (w x - F x (z x))) := by
    abel
  have hdef : ‖(u x - F x (y x)) - (w x - F x (z x))‖ ≤ ηy + ηz :=
    (norm_sub_le _ _).trans (add_le_add (hyd x hx) (hzd x hx))
  by_cases hx0 : y x - z x = 0
  · -- the trajectories meet: the fields agree and only the defects remain
    have hyz : y x = z x := sub_eq_zero.1 hx0
    have hnorm : ‖u x - w x‖ < r := by
      have hF0 : F x (y x) - F x (z x) = 0 := by rw [hyz, sub_self]
      rw [hsplit, hF0, zero_add]
      refine lt_of_le_of_lt hdef ?_
      simpa [hx0] using hr
    exact he.liminf_right_slope_norm_le hnorm
  · -- the norm is differentiable and its derivative is controlled by the one-sided bound
    have hd := hasDerivWithinAt_norm_of_ne he hx0
    have hpos : 0 < ‖y x - z x‖ := norm_pos_iff.2 hx0
    have hinner :
        ⟪y x - z x, u x - w x⟫ ≤ ℓ * ‖y x - z x‖ ^ 2 + ‖y x - z x‖ * (ηy + ηz) := by
      rw [hsplit, inner_add_right, real_inner_comm]
      have h1 := hF x hx
      have h2 := real_inner_le_norm (y x - z x) ((u x - F x (y x)) - (w x - F x (z x)))
      have h3 := mul_le_mul_of_nonneg_left hdef (norm_nonneg (y x - z x))
      linarith
    have hle : ⟪y x - z x, u x - w x⟫ / ‖y x - z x‖ ≤ ℓ * ‖y x - z x‖ + (ηy + ηz) := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have := hd.liminf_right_slope_le (lt_of_le_of_lt hle hr)
    simpa [slope_def_module, smul_eq_mul] using this

/-- **Stability for one-sided Lipschitz fields (approximate solutions).**  If `F` is one-sided
Lipschitz with constant `ℓ ∈ ℝ`, `y' = u`, `z' = w` with `‖u - F(y)‖ ≤ ηy`, `‖w - F(z)‖ ≤ ηz`
and `‖y a - z a‖ ≤ δ`, then `‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a)`
(Carrel–Vandereycken, arXiv 2312.00172, Theorem 7, in the abstract form). -/
theorem norm_sub_le_gronwallBound_of_oneSided {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a) :=
  norm_sub_le_gronwallBound_of_inner_le (fun t _ => hF t (y t) (z t)) hyc hy hyd hzc hz hzd h0

/-- **Localised stability** (Hu–Yu, arXiv 2610.41606, §3): if `F` is one-sided Lipschitz with
constant `ℓ` on a set `K` and both (approximate) trajectories remain in `K`, the stability bound
`‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a)` holds, without any Lipschitz bound. -/
theorem norm_sub_le_gronwallBound_of_oneSidedOn {F : ℝ → E → E} {K : Set E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzOn F K ℓ) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyK : ∀ t ∈ Ico a b, y t ∈ K) (hzK : ∀ t ∈ Ico a b, z t ∈ K)
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a) :=
  norm_sub_le_gronwallBound_of_inner_le (fun t ht => hF t _ (hyK t ht) _ (hzK t ht))
    hyc hy hyd hzc hz hzd h0

/-! ### Explicit forms of the Grönwall bound for arbitrary real rates -/

/-- For a nonpositive rate `K ≤ 0`: `gronwallBound δ K η x ≤ δ exp (K x) + η x` (any `x`). -/
lemma gronwallBound_le_of_nonpos {δ K η x : ℝ} (hK : K ≤ 0) (hη : 0 ≤ η) :
    gronwallBound δ K η x ≤ δ * Real.exp (K * x) + η * x := by
  rcases hK.lt_or_eq with hK' | rfl
  · rw [gronwallBound_of_K_ne_0 hK'.ne]
    have h1 : (Real.exp (K * x) - 1) / K ≤ x := by
      rw [div_le_iff_of_neg hK']
      linarith [Real.add_one_le_exp (K * x), mul_comm x K]
    have h2 : η / K * (Real.exp (K * x) - 1) = η * ((Real.exp (K * x) - 1) / K) := by ring
    simp only
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 hη]
  · simp [gronwallBound_K0]

/-- **Time-uniform bound** for a negative rate `K < 0`:
`gronwallBound δ K η x ≤ δ exp (K x) + η / (-K)` (any `x`).  This is the source of error bounds
for dissipative problems that do not grow with the length of the time interval. -/
lemma gronwallBound_le_of_neg {δ K η x : ℝ} (hK : K < 0) (hη : 0 ≤ η) :
    gronwallBound δ K η x ≤ δ * Real.exp (K * x) + η / (-K) := by
  rw [gronwallBound_of_K_ne_0 hK.ne]
  simp only
  have h1 : η / K * (Real.exp (K * x) - 1) = η / (-K) * (1 - Real.exp (K * x)) := by
    rw [div_neg]; ring
  have h2 : 0 ≤ η / (-K) := div_nonneg hη (neg_nonneg.2 hK.le)
  rw [h1]
  nlinarith [Real.exp_pos (K * x), mul_nonneg h2 (Real.exp_pos (K * x)).le]

/-- Explicit Grönwall bound valid for **every real rate** `K`:
`gronwallBound δ K η x ≤ exp (K x) δ + η x max 1 (exp (K x))` for `η, x ≥ 0`. -/
lemma gronwallBound_le_exp_mul_add_max {δ K η x : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) :
    gronwallBound δ K η x ≤ Real.exp (K * x) * δ + η * x * max 1 (Real.exp (K * x)) := by
  have hηx : 0 ≤ η * x := mul_nonneg hη hx
  rcases le_total K 0 with hK | hK
  · calc gronwallBound δ K η x ≤ δ * Real.exp (K * x) + η * x := gronwallBound_le_of_nonpos hK hη
      _ ≤ Real.exp (K * x) * δ + η * x * max 1 (Real.exp (K * x)) := by
        rw [mul_comm δ]
        nlinarith [mul_le_mul_of_nonneg_left (le_max_left 1 (Real.exp (K * x))) hηx]
  · calc gronwallBound δ K η x ≤ Real.exp (K * x) * (δ + η * x) := gronwallBound_le_exp_mul hK hη
      _ ≤ Real.exp (K * x) * δ + η * x * max 1 (Real.exp (K * x)) := by
        nlinarith [mul_le_mul_of_nonneg_left (le_max_right 1 (Real.exp (K * x))) hηx]

omit [InnerProductSpace ℝ E] in
/-- The defect bound is nonnegative as soon as the time interval is nondegenerate. -/
private lemma defect_nonneg {F : ℝ → E → E} {y u : ℝ → E} {a b η t : ℝ}
    (h : ∀ s ∈ Ico a b, ‖u s - F s (y s)‖ ≤ η) (ht : t ∈ Icc a b) (hat : a < t) : 0 ≤ η :=
  (norm_nonneg _).trans (h a ⟨le_rfl, hat.trans_le ht.2⟩)

/-- **Stability with defects, explicit form for every real `ℓ`.**  Under the hypotheses of
`norm_sub_le_gronwallBound_of_oneSided`,
`‖y t - z t‖ ≤ exp (ℓ (t-a)) δ + (ηy + ηz) (t - a) max 1 (exp (ℓ (t-a)))`. -/
theorem norm_sub_le_exp_add_max_of_oneSided {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤
      Real.exp (ℓ * (t - a)) * δ + (ηy + ηz) * (t - a) * max 1 (Real.exp (ℓ * (t - a))) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided hF hyc hy hyd hzc hz hzd h0 t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · simpa [gronwallBound_x0] using h
  · exact h.trans (gronwallBound_le_exp_mul_add_max
      (add_nonneg (defect_nonneg hyd ht hat) (defect_nonneg hzd ht hat)) (sub_nonneg.2 ht.1))

/-- **Stability with defects, `ℓ ≥ 0`:**
`‖y t - z t‖ ≤ exp (ℓ (t-a)) (δ + (ηy + ηz) (t - a))`. -/
theorem norm_sub_le_exp_mul_add_of_oneSided {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hℓ : 0 ≤ ℓ) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * (δ + (ηy + ηz) * (t - a)) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided hF hyc hy hyd hzc hz hzd h0 t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · simpa [gronwallBound_x0] using h
  · exact h.trans (gronwallBound_le_exp_mul hℓ
      (add_nonneg (defect_nonneg hyd ht hat) (defect_nonneg hzd ht hat)))

/-- **Stability with defects, dissipative case `ℓ ≤ 0`:**
`‖y t - z t‖ ≤ exp (ℓ (t-a)) δ + (ηy + ηz) (t - a)`. -/
theorem norm_sub_le_exp_add_of_oneSided_nonpos {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ ≤ 0) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * δ + (ηy + ηz) * (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided hF hyc hy hyd hzc hz hzd h0 t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · simpa [gronwallBound_x0] using h
  · rw [mul_comm (Real.exp _)]
    exact h.trans (gronwallBound_le_of_nonpos hℓ
      (add_nonneg (defect_nonneg hyd ht hat) (defect_nonneg hzd ht hat)))

/-- **Time-uniform stability for strictly dissipative fields `ℓ < 0`:**
`‖y t - z t‖ ≤ exp (ℓ (t-a)) δ + (ηy + ηz) / (-ℓ)`; the defects are damped and the error does not
accumulate over long times. -/
theorem norm_sub_le_exp_add_div_of_oneSided_neg {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ < 0) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - F t (y t)‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - F t (z t)‖ ≤ ηz) (hη : 0 ≤ ηy + ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * δ + (ηy + ηz) / (-ℓ) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided hF hyc hy hyd hzc hz hzd h0 t ht
  rcases ht.1.eq_or_lt with rfl | hat
  · simp only [gronwallBound_x0, sub_self, mul_zero, Real.exp_zero, one_mul] at h ⊢
    linarith [div_nonneg hη (neg_nonneg.2 hℓ.le)]
  · rw [mul_comm (Real.exp _)]
    exact h.trans (gronwallBound_le_of_neg hℓ hη)

/-! ### Exact solutions -/

namespace ODESolution

variable {F G : ℝ → E → E} {ℓ : ℝ} {y z : ℝ → E} {a b : ℝ}

/-- Exponential stability of exact solutions, assuming the one-sided inequality along the two
trajectories: `‖y t - z t‖ ≤ exp (ℓ (t - a)) ‖y a - z a‖`. -/
theorem norm_sub_le_exp_of_inner_le (hy : ODESolution F y a b) (hz : ODESolution F z a b)
    (hF : ∀ t ∈ Ico a b, ⟪F t (y t) - F t (z t), y t - z t⟫ ≤ ℓ * ‖y t - z t‖ ^ 2) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a - z a‖ := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_inner_le (ηy := 0) (ηz := 0) hF hy.cont hy.deriv
    (fun _ _ => by simp) hz.cont hz.deriv (fun _ _ => by simp) le_rfl t ht
  rwa [add_zero, gronwallBound_ε0, mul_comm] at h

/-- **Stability of the exact flow of a one-sided Lipschitz field** (any real `ℓ`):
`‖y t - z t‖ ≤ exp (ℓ (t - a)) ‖y a - z a‖`.  For `ℓ < 0` this is exponential contraction,
independently of the Lipschitz constant (Hu–Yu, arXiv 2610.41606, §3;
Carrel–Vandereycken, arXiv 2312.00172, Theorem 7 with `ε = 0`). -/
theorem norm_sub_le_exp_of_oneSided (hy : ODESolution F y a b) (hz : ODESolution F z a b)
    (hF : IsOneSidedLipschitzField F ℓ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a - z a‖ :=
  hy.norm_sub_le_exp_of_inner_le hz fun t _ => hF t (y t) (z t)

/-- Localised version: exponential stability for solutions remaining in a set `K` on which `F`
is one-sided Lipschitz (Hu–Yu, arXiv 2610.41606, §3, `e(t) ≤ exp(μ t) e(0)`). -/
theorem norm_sub_le_exp_of_oneSidedOn {K : Set E} (hy : ODESolution F y a b)
    (hz : ODESolution F z a b) (hF : IsOneSidedLipschitzOn F K ℓ)
    (hyK : ∀ t ∈ Ico a b, y t ∈ K) (hzK : ∀ t ∈ Ico a b, z t ∈ K) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a - z a‖ :=
  hy.norm_sub_le_exp_of_inner_le hz fun t ht => hF t _ (hyK t ht) _ (hzK t ht)

/-- **Forward uniqueness** for one-sided Lipschitz fields (no Lipschitz bound needed). -/
theorem eqOn_of_oneSided (hy : ODESolution F y a b) (hz : ODESolution F z a b)
    (hF : IsOneSidedLipschitzField F ℓ) (h0 : y a = z a) : EqOn y z (Icc a b) := by
  intro t ht
  have h := hy.norm_sub_le_exp_of_oneSided hz hF t ht
  rw [h0, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Non-expansiveness of dissipative flows**: if `ℓ ≤ 0` then
`‖y t - z t‖ ≤ ‖y a - z a‖` for all `t ∈ [a, b]`. -/
theorem norm_sub_le_of_oneSided_nonpos (hy : ODESolution F y a b) (hz : ODESolution F z a b)
    (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ ≤ 0) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ ‖y a - z a‖ := by
  intro t ht
  have h := hy.norm_sub_le_exp_of_oneSided hz hF t ht
  have hexp : Real.exp (ℓ * (t - a)) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hℓ (sub_nonneg.2 ht.1))
  calc ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a - z a‖ := h
    _ ≤ 1 * ‖y a - z a‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ = ‖y a - z a‖ := one_mul _

/-- **Error of a perturbed problem** (abstract DLRA error bound).  Let `A` solve `A' = F(t, A)`
with `F` one-sided Lipschitz with constant `ℓ ∈ ℝ`, and let `Y` solve a perturbed problem
`Y' = G(t, Y)` with `‖G(t, Y t) - F(t, Y t)‖ ≤ ε` along `Y`.  Then
`‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ε (t - a) = e^{ℓ(t-a)} δ + (t-a) φ₁(ℓ(t-a)) ε`.
For DLRA, `G(t, Y) = P(Y) F(t, Y)` and `ε` bounds the normal component `‖(I - P(Y)) F(t, Y)‖`
(Carrel–Vandereycken, arXiv 2312.00172, Theorem 7). -/
theorem norm_sub_le_of_perturbed {A Y : ℝ → E} {ε : ℝ} (hA : ODESolution F A a b)
    (hY : ODESolution G Y a b) (hF : IsOneSidedLipschitzField F ℓ)
    (hdef : ∀ t ∈ Ico a b, ‖G t (Y t) - F t (Y t)‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ε (t - a) := by
  intro t ht
  have h := norm_sub_le_gronwallBound_of_oneSided (ηz := 0) hF hY.cont hY.deriv hdef
    hA.cont hA.deriv (fun _ _ => by simp) le_rfl t ht
  rwa [add_zero] at h

/-- Explicit form of `norm_sub_le_of_perturbed`, valid for every real `ℓ`:
`‖Y t - A t‖ ≤ exp (ℓ (t - a)) ‖Y a - A a‖ + ε (t - a) max 1 (exp (ℓ (t - a)))`. -/
theorem norm_sub_le_of_perturbed_max {A Y : ℝ → E} {ε : ℝ} (hA : ODESolution F A a b)
    (hY : ODESolution G Y a b) (hF : IsOneSidedLipschitzField F ℓ) (hε : 0 ≤ ε)
    (hdef : ∀ t ∈ Ico a b, ‖G t (Y t) - F t (Y t)‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤
      Real.exp (ℓ * (t - a)) * ‖Y a - A a‖ + ε * (t - a) * max 1 (Real.exp (ℓ * (t - a))) :=
  fun t ht => (hA.norm_sub_le_of_perturbed hY hF hdef t ht).trans
    (gronwallBound_le_exp_mul_add_max hε (sub_nonneg.2 ht.1))

/-- **Time-uniform error bound for strictly dissipative problems** (`ℓ < 0`): under the
hypotheses of `norm_sub_le_of_perturbed`,
`‖Y t - A t‖ ≤ exp (ℓ (t - a)) ‖Y a - A a‖ + ε / (-ℓ)`, uniformly in the length of the time
interval and independently of any Lipschitz constant. -/
theorem norm_sub_le_of_perturbed_of_neg {A Y : ℝ → E} {ε : ℝ} (hA : ODESolution F A a b)
    (hY : ODESolution G Y a b) (hF : IsOneSidedLipschitzField F ℓ) (hℓ : ℓ < 0) (hε : 0 ≤ ε)
    (hdef : ∀ t ∈ Ico a b, ‖G t (Y t) - F t (Y t)‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ Real.exp (ℓ * (t - a)) * ‖Y a - A a‖ + ε / (-ℓ) :=
  fun t ht => by
    rw [mul_comm]
    exact (hA.norm_sub_le_of_perturbed hY hF hdef t ht).trans (gronwallBound_le_of_neg hℓ hε)

end ODESolution

/-! ### Galerkin trajectories -/

section Galerkin

variable {F : ℝ → E → E} {ℓ : ℝ} {P : E →L[ℝ] E}

/-- A Galerkin trajectory `y' = P (G t y)` started in the range of the projector stays there. -/
private lemma galerkin_proj_eq (hP : IsOrthProj P) {G : ℝ → E → E} {y : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun t x => P (G t x)) y a b) (h0 : P (y a) = y a) :
    ∀ t ∈ Icc a b, P (y t) = y t := by
  intro t ht
  have hgc : ContinuousOn (fun s => y s - P (y s)) (Icc a b) :=
    hy.cont.sub (P.continuous.comp_continuousOn hy.cont)
  have hgd : ∀ s ∈ Ico a b, HasDerivWithinAt (fun s => y s - P (y s)) 0 (Ici s) s := by
    intro s hs
    have h1 := hy.deriv s hs
    have h2 := P.hasFDerivAt.comp_hasDerivWithinAt s h1
    convert h1.sub h2 using 1
    all_goals first | rfl | rw [hP.idem, sub_self]
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment hgc hgd (C := 0)
    (fun _ _ => by simp) t ht
  rw [h0, sub_self, sub_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

/-- **Stability of approximate Galerkin trajectories.**  If `F` is one-sided Lipschitz with
constant `ℓ`, `P` is an orthogonal projector, the trajectories `y, z` stay in the range of `P`
and solve `y' = P F(t, y)`, `z' = P F(t, z)` up to defects `ηy`, `ηz`, then
`‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a)`: Galerkin approximation does not degrade
the one-sided Lipschitz constant (even though `P ∘ F` need not be one-sided Lipschitz with `ℓ`
off the range of `P`). -/
theorem galerkin_norm_sub_le_gronwallBound (hF : IsOneSidedLipschitzField F ℓ)
    (hP : IsOrthProj P) {y z u w : ℝ → E} {a b ηy ηz δ : ℝ}
    (hyP : ∀ t ∈ Ico a b, P (y t) = y t) (hzP : ∀ t ∈ Ico a b, P (z t) = z t)
    (hyc : ContinuousOn y (Icc a b)) (hy : ∀ t ∈ Ico a b, HasDerivWithinAt y (u t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, ‖u t - P (F t (y t))‖ ≤ ηy)
    (hzc : ContinuousOn z (Icc a b)) (hz : ∀ t ∈ Ico a b, HasDerivWithinAt z (w t) (Ici t) t)
    (hzd : ∀ t ∈ Ico a b, ‖w t - P (F t (z t))‖ ≤ ηz) (h0 : ‖y a - z a‖ ≤ δ) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ gronwallBound δ ℓ (ηy + ηz) (t - a) :=
  norm_sub_le_gronwallBound_of_inner_le (F := fun t x => P (F t x))
    (fun t ht => hF.inner_proj_sub_le hP t (hyP t ht) (hzP t ht)) hyc hy hyd hzc hz hzd h0

/-- **Exponential stability of Galerkin trajectories.**  Two solutions of the Galerkin ODE
`y' = P F(t, y)` started in the range of the orthogonal projector `P` satisfy
`‖y t - z t‖ ≤ exp (ℓ (t - a)) ‖y a - z a‖`, with the one-sided Lipschitz constant `ℓ` of the
full field `F`. -/
theorem ODESolution.galerkin_norm_sub_le_exp (hF : IsOneSidedLipschitzField F ℓ)
    (hP : IsOrthProj P) {y z : ℝ → E} {a b : ℝ}
    (hy : ODESolution (fun t x => P (F t x)) y a b) (hz : ODESolution (fun t x => P (F t x)) z a b)
    (hy0 : P (y a) = y a) (hz0 : P (z a) = z a) :
    ∀ t ∈ Icc a b, ‖y t - z t‖ ≤ Real.exp (ℓ * (t - a)) * ‖y a - z a‖ :=
  hy.norm_sub_le_exp_of_oneSidedOn hz (hF.proj hP)
    (fun t ht => galerkin_proj_eq hP hy hy0 t (Ico_subset_Icc_self ht))
    (fun t ht => galerkin_proj_eq hP hz hz0 t (Ico_subset_Icc_self ht))

/-- **Robust Galerkin error bound.**  Let `A` solve `A' = F(t, A)` with `F` one-sided Lipschitz
with constant `ℓ`, and `Y` the Galerkin trajectory `Y' = P F(t, Y)`.  If the neglected component
satisfies `‖F(t, Y t) - P F(t, Y t)‖ ≤ ε` along `Y`, then
`‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ε (t - a) = e^{ℓ(t-a)} δ + (t-a) φ₁(ℓ(t-a)) ε`
(fixed-projector instance of Carrel–Vandereycken, arXiv 2312.00172, Theorem 7). -/
theorem ODESolution.galerkin_norm_sub_le_of_normal {A Y : ℝ → E} {a b ε : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) (hA : ODESolution F A a b)
    (hY : ODESolution (fun t x => P (F t x)) Y a b)
    (hε : ∀ t ∈ Ico a b, ‖F t (Y t) - P (F t (Y t))‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖Y t - A t‖ ≤ gronwallBound ‖Y a - A a‖ ℓ ε (t - a) :=
  ODESolution.norm_sub_le_of_perturbed hA hY hF fun t ht => by
    rw [norm_sub_rev]; exact hε t ht

end Galerkin

/-! ### Implicit (Galerkin) Euler steps -/

/-- Scalar step: `e² ≤ e D + c e²` with `e, D ≥ 0` implies `(1 - c) e ≤ D`. -/
private lemma one_sub_mul_le_of_sq_le {e D c : ℝ} (he : 0 ≤ e) (hD : 0 ≤ D)
    (h : e ^ 2 ≤ e * D + c * e ^ 2) : (1 - c) * e ≤ D := by
  rcases he.eq_or_lt with rfl | hpos
  · simpa using hD
  · have h' : ((1 - c) * e) * e ≤ D * e := by nlinarith
    exact le_of_mul_le_mul_right h' hpos

/-- **Stability of a projected implicit step.**  Let `P` be an orthogonal projector, `h ≥ 0`,
`x₁ = P (x₀ + h f)`, `y₁ = P (y₀ + h g)`, where the increments satisfy the one-sided inequality
`⟪f - g, x₁ - y₁⟫ ≤ ℓ ‖x₁ - y₁‖²` (for an implicit step `f = F(t, x₁)`, `g = F(t, y₁)`).  Then
`(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖`. -/
theorem proj_implicit_step_stability {P : E →L[ℝ] E} (hP : IsOrthProj P) {h ℓ : ℝ}
    (hh : 0 ≤ h) {x₀ y₀ x₁ y₁ f g : E} (hx : x₁ = P (x₀ + h • f)) (hy : y₁ = P (y₀ + h • g))
    (hfg : ⟪f - g, x₁ - y₁⟫ ≤ ℓ * ‖x₁ - y₁‖ ^ 2) :
    (1 - h * ℓ) * ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖ := by
  have he : x₁ - y₁ = P ((x₀ - y₀) + h • (f - g)) := by
    rw [hx, hy, ← map_sub, smul_sub]
    congr 1
    abel
  have hPe : P (x₁ - y₁) = x₁ - y₁ := by rw [he, hP.idem]
  have key : ‖x₁ - y₁‖ ^ 2 = ⟪x₀ - y₀, x₁ - y₁⟫ + h * ⟪f - g, x₁ - y₁⟫ := by
    have h1 : ⟪x₁ - y₁, x₁ - y₁⟫ = ⟪P ((x₀ - y₀) + h • (f - g)), x₁ - y₁⟫ := by rw [← he]
    rw [← real_inner_self_eq_norm_sq, h1, hP.symm, hPe, inner_add_left, real_inner_smul_left]
  have h2 := real_inner_le_norm (x₀ - y₀) (x₁ - y₁)
  have h3 := mul_le_mul_of_nonneg_left hfg hh
  refine one_sub_mul_le_of_sq_le (norm_nonneg _) (norm_nonneg _) ?_
  nlinarith

/-- **Implicit Euler step with residuals** (Hu–Yu, arXiv 2610.41606, eq. (5.7)): if
`x₁ = x₀ + h F(t, x₁) + r` and `y₁ = y₀ + h F(t, y₁) + s` with `h ≥ 0`, and `F(t, ·)` satisfies
the one-sided inequality with constant `ℓ` at the pair `(x₁, y₁)`, then
`(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖ + ‖r - s‖`. -/
theorem implicitEuler_stability {F : ℝ → E → E} {ℓ h t : ℝ} (hh : 0 ≤ h) {x₀ y₀ x₁ y₁ r s : E}
    (hF : ⟪F t x₁ - F t y₁, x₁ - y₁⟫ ≤ ℓ * ‖x₁ - y₁‖ ^ 2)
    (hx : x₁ = x₀ + h • F t x₁ + r) (hy : y₁ = y₀ + h • F t y₁ + s) :
    (1 - h * ℓ) * ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖ + ‖r - s‖ := by
  have hx' : x₁ = (1 : E →L[ℝ] E) ((x₀ + r) + h • F t x₁) := by
    change x₁ = (x₀ + r) + h • F t x₁
    conv_lhs => rw [hx]
    abel
  have hy' : y₁ = (1 : E →L[ℝ] E) ((y₀ + s) + h • F t y₁) := by
    change y₁ = (y₀ + s) + h • F t y₁
    conv_lhs => rw [hy]
    abel
  refine (proj_implicit_step_stability IsOrthProj.one hh hx' hy' hF).trans ?_
  have : x₀ + r - (y₀ + s) = (x₀ - y₀) + (r - s) := by abel
  rw [this]
  exact norm_add_le _ _

/-- **Uniqueness of the implicit stage** (Hu–Yu, arXiv 2610.41606, proof of Theorem 5.1): if
`h ℓ < 1`, the equation `x = x₀ + h F(t, x) + r` has at most one solution among states where the
one-sided inequality holds. -/
theorem implicitEuler_unique {F : ℝ → E → E} {ℓ h t : ℝ} (hh : 0 ≤ h) (hhℓ : h * ℓ < 1)
    {x₀ x₁ y₁ r : E} (hF : ⟪F t x₁ - F t y₁, x₁ - y₁⟫ ≤ ℓ * ‖x₁ - y₁‖ ^ 2)
    (hx : x₁ = x₀ + h • F t x₁ + r) (hy : y₁ = x₀ + h • F t y₁ + r) : x₁ = y₁ := by
  have h1 := implicitEuler_stability hh hF hx hy
  rw [sub_self, sub_self, norm_zero, add_zero] at h1
  have h2 : ‖x₁ - y₁‖ ≤ 0 := by nlinarith [norm_nonneg (x₁ - y₁)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)

/-- **Stability of the implicit Galerkin Euler step** `x₁ = P (x₀ + h F(t, x₁))` for a one-sided
Lipschitz field: `(1 - h ℓ) ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖`.  For dissipative `F` (`ℓ ≤ 0`) the step is
non-expansive, for every step size `h ≥ 0`. -/
theorem galerkin_implicitEuler_stability {F : ℝ → E → E} {ℓ : ℝ}
    (hF : IsOneSidedLipschitzField F ℓ) {P : E →L[ℝ] E} (hP : IsOrthProj P) {h t : ℝ}
    (hh : 0 ≤ h) {x₀ y₀ x₁ y₁ : E} (hx : x₁ = P (x₀ + h • F t x₁))
    (hy : y₁ = P (y₀ + h • F t y₁)) :
    (1 - h * ℓ) * ‖x₁ - y₁‖ ≤ ‖x₀ - y₀‖ :=
  proj_implicit_step_stability hP hh hx hy (hF t x₁ y₁)

/-- **Norm decay of the implicit Galerkin Euler step** (Appelö–Cheng, arXiv 2402.05347,
Theorem 3.1, Galerkin part, generalised to `⟪F(t, x), x⟫ ≤ ℓ ‖x‖²`): if `x₁ = P (x₀ + h F(t, x₁))`
then `(1 - h ℓ) ‖x₁‖ ≤ ‖x₀‖`; in particular `‖x₁‖ ≤ ‖x₀‖` for dissipative fields
(`⟪F(t, X), X⟫ ≤ 0`). -/
theorem galerkin_implicitEuler_norm_le {F : ℝ → E → E} {ℓ h t : ℝ} {P : E →L[ℝ] E}
    (hP : IsOrthProj P) (hh : 0 ≤ h) {x₀ x₁ : E} (hF : ⟪F t x₁, x₁⟫ ≤ ℓ * ‖x₁‖ ^ 2)
    (hx : x₁ = P (x₀ + h • F t x₁)) : (1 - h * ℓ) * ‖x₁‖ ≤ ‖x₀‖ := by
  have h0 : (0 : E) = P (0 + h • (0 : E)) := by simp
  have := proj_implicit_step_stability (ℓ := ℓ) hP hh hx h0 (by simpa using hF)
  simpa using this

/-- Dissipative case of `galerkin_implicitEuler_norm_le` (Appelö–Cheng, arXiv 2402.05347,
Theorem 3.1): if `⟪F(t, X), X⟫ ≤ 0` for all `X`, the implicit Galerkin Euler step
`x₁ = P (x₀ + h F(t, x₁))` satisfies `‖x₁‖ ≤ ‖x₀‖`. -/
theorem galerkin_implicitEuler_norm_le_of_dissipative {F : ℝ → E → E} {h t : ℝ}
    {P : E →L[ℝ] E} (hP : IsOrthProj P) (hh : 0 ≤ h) (hF : ∀ x, ⟪F t x, x⟫ ≤ 0) {x₀ x₁ : E}
    (hx : x₁ = P (x₀ + h • F t x₁)) : ‖x₁‖ ≤ ‖x₀‖ := by
  have := galerkin_implicitEuler_norm_le (ℓ := 0) hP hh (by simpa using hF x₁) hx
  simpa using this

/-! ### An example with a negative one-sided Lipschitz constant -/

/-- The hypotheses of `ODESolution.norm_sub_le_exp_of_oneSided` are satisfiable with a negative
constant: `y t = exp (-t)` and `z t = 0` both solve `y' = -y`, which is one-sided Lipschitz with
`ℓ = -1`, and the theorem yields exponential decay of `y - z`. -/
example :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖Real.exp (-t) - 0‖ ≤ Real.exp (-1 * (t - 0)) * ‖Real.exp (-0) - 0‖ := by
  have hy : ODESolution (fun _ (x : ℝ) => (-1 : ℝ) • x) (fun t => Real.exp (-t)) 0 1 :=
    { cont := (Real.continuous_exp.comp continuous_neg).continuousOn
      deriv := fun t _ => by
        have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).hasDerivWithinAt
          (s := Ici t)
        convert this using 1
        all_goals first | rfl | simp [mul_comm] }
  have hz : ODESolution (fun _ (x : ℝ) => (-1 : ℝ) • x) (fun _ => (0 : ℝ)) 0 1 :=
    { cont := continuousOn_const
      deriv := fun t _ => by simpa using hasDerivWithinAt_const t (Ici t) (0 : ℝ) }
  exact hy.norm_sub_le_exp_of_oneSided hz (isOneSidedLipschitzField_smul_id (-1))

end LeanDLRA
